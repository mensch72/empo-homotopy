"""Robot side given U, residual of the full system in log-space, Newton, Result.

Unknowns: z = log x, x = -Q, for the non-terminal states only (n = |nt|*A entries, state-major).
Then pi(s) = softmax(-beta z(s)) (never formed as 1-pi; see Result.one_minus_pi) and the residual is
    R(z) = log( gamma_r * K (c + w) ) - z,   c = -U(pi),  w(s) = sum_a pi(s,a) x(s,a) (Lehmer mean; 0 at terminal states),
which vanishes iff (pi, Q = -x, Vr = -(c+w)) solves the system of STATEMENTS s0.  Everything is complex-step safe;
Jacobians are exact to machine precision (no finite differences).
"""
from collections import namedtuple
from dataclasses import dataclass, field
import numpy as np

Params = namedtuple("Params", "beta gamma_r gh")        # gh: override of every gamma_h (None = use the variant's)
FIELD = {"beta": "beta", "gamma_r": "gamma_r", "gamma_h": "gh"}


def params_of(game, **kw):
    return Params(game.beta, game.gamma_r, None)._replace(**{FIELD[k]: v for k, v in kw.items()})


def lse(l):
    m = np.max(l.real, axis=-1, keepdims=True)
    return (m + np.log(np.exp(l - m).sum(-1, keepdims=True)))[..., 0]


def softmax_full(game, zz, beta):
    """pi (S,A) from log x of the non-terminal states (terminal rows uniform)."""
    l = -beta * zz
    pn = np.exp(l - lse(l)[:, None])
    pi = np.full((game.S, game.A), 1.0 / game.A, dtype=pn.dtype)
    pi[game.nt] = pn
    return pi


def state(game, z, p):
    """(R, pi, U, aux) at log-unknowns z and parameters p."""
    with np.errstate(all='ignore'):
        zz = np.asarray(z).reshape(len(game.nt), game.A)
        pi = softmax_full(game, zz, p.beta)
        U, aux = game.human.evaluate(pi, p.gh)
        w = np.zeros(game.S, dtype=pi.dtype)
        w[game.nt] = np.exp(lse((1 - p.beta) * zz) - lse(-p.beta * zz))
        N = p.gamma_r * game.K[game.nt].reshape(-1, game.S) @ (-U + w)
        N = np.where(N.real > 0, N, np.nan)
        return np.log(N) - zz.ravel(), pi, U, aux


def residual(game, z, p):
    return state(game, z, p)[0]


def jacobian(game, z, p, param=None, h=1e-30):
    """(Jz, Jlam) by complex step; Jlam w.r.t. `param` ('beta'|'gamma_r'|'gamma_h') if given."""
    z = np.asarray(z, float)
    n = len(z)
    Jz = np.empty((n, n))
    zc = z.astype(complex)
    for j in range(n):
        zc[j] += 1j * h
        Jz[:, j] = residual(game, zc, p).imag / h
        zc[j] -= 1j * h
    if param is None:
        return Jz
    val = getattr(p, FIELD[param])
    if val is None:
        val = game.human.gamma_h[0]
    Jl = residual(game, z, p._replace(**{FIELD[param]: val + 1j * h})).imag / h
    return Jz, Jl


def robot_given_pi(game, pi, U):
    """Q, Vr for a given pi and U: Vr = U + gamma_r P_pi Vr (linear solve), Q = gamma_r K Vr."""
    P = np.einsum('sa,sat->st', pi, game.K)
    Vr = np.linalg.solve(np.eye(game.S) - game.gamma_r * P, U)
    return game.gamma_r * game.K @ Vr, Vr


def newton(game, z0, p, tol=1e-12, maxit=60):
    """Damped Newton on R(z) = 0.  Returns (z, max|R|, iterations, converged)."""
    z = np.array(z0, float)
    R = residual(game, z, p)
    for it in range(maxit):
        nr = np.abs(R).max()
        if not np.isfinite(nr):
            return z, nr, it, False
        if nr < tol:
            return z, nr, it, True
        try:
            d = -np.linalg.solve(jacobian(game, z, p), R)
        except np.linalg.LinAlgError:
            return z, nr, it, False
        if not np.all(np.isfinite(d)):
            return z, nr, it, False
        d *= min(1.0, 4.0 / np.abs(d).max())
        t = 1.0
        while t > 1e-4:
            R2 = residual(game, z + t * d, p)
            if np.isfinite(R2).all() and np.abs(R2).max() < (1 - 1e-4 * t) * nr:
                break
            t /= 2
        else:
            return z, nr, it, False
        z, R = z + t * d, R2
    nr = np.abs(R).max()
    return z, nr, maxit, bool(nr < tol)


@dataclass
class Result:
    game: object
    pi: np.ndarray
    Q: np.ndarray
    Vr: np.ndarray
    U: np.ndarray
    residual: float
    iterations: int
    success: bool
    method: str
    notes: str = ""
    z: np.ndarray = None            # log(-Q) of the non-terminal states, flattened
    params: Params = None

    def one_minus_pi(self):
        """1 - pi(s,a) from the logits, as sum_{b != a} pi(s,b) (no cancellation near pi = 1)."""
        g = self.game
        out = np.full((g.S, g.A), 1 - 1.0 / g.A)
        zz = self.z.reshape(len(g.nt), g.A)
        l = -self.params.beta * zz
        for k, s in enumerate(g.nt):
            for a in range(g.A):
                rest = np.delete(l[k], a)
                out[s, a] = np.exp(lse(rest) - lse(l[k])) if rest.size else 0.0
        return out

    def summary(self):
        return (f"[{self.method}] success={self.success} residual={self.residual:.2e} its={self.iterations}\n"
                f"  pi={np.array2string(self.pi, precision=6)}\n  U={np.array2string(self.U, precision=6)}"
                + (f"\n  notes: {self.notes}" if self.notes else ""))


def make_result(game, z, p, method, iterations=0, success=None, notes=""):
    z = np.asarray(z, float)
    R, pi, U, aux = state(game, z, p)
    res = float(np.abs(R).max()) if np.isfinite(R).all() else float("inf")
    if np.all(np.isfinite(U)) and np.all(U < 0):
        Q, Vr = robot_given_pi(game.with_params(beta=p.beta, gamma_r=p.gamma_r), pi, U)
    else:
        Q, Vr = np.full((game.S, game.A), np.nan), np.full(game.S, np.nan)
    return Result(game, pi, Q, Vr, U, res, iterations, res < 1e-9 if success is None else success, method, notes, z, p)


def ranks(game):
    """Topological rank rho (rho(s') < rho(s) for every edge s -> s') w.r.t. robot K and the variant's kernels,
    or None if the successor graph has a cycle (self-loops included)."""
    E = (game.K.any(axis=1)) | game.human.support()
    S = game.S
    rho = -np.ones(S, int)
    left = set(range(S))
    r = 0
    while left:
        ready = [s for s in left if not any(E[s, t] for t in left)]
        if not ready:
            return None
        for s in ready:
            rho[s] = r
        left -= set(ready)
        r += 1
    return rho
