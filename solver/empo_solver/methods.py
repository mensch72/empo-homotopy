"""Solution methods: acyclic backward induction, finite-horizon unrolling, arclength continuation, multistart, front end."""
from dataclasses import dataclass, field
import numpy as np
from scipy.optimize import root
from .core import (Params, params_of, residual, jacobian, newton, make_result, ranks, z_from_pi, lse,
                   softmax_full, robot_given_pi, Result)


class CyclicError(ValueError):
    pass


def _uniform(game):
    return np.full((game.S, game.A), 1.0 / game.A)


def _powerlaw(game, Q):
    """pi(s) ∝ (-Q(s,a))^(-beta) on non-terminal states (log-space), uniform on terminal ones."""
    pi = _uniform(game)
    zz = np.log(-Q[game.nt])
    l = -game.beta * zz
    pi[game.nt] = np.exp(l - lse(l)[:, None])
    return pi


# ---------------------------------------------------------------- (a) acyclic
def solve_acyclic(game):
    """Exact backward induction by topological rank (STATEMENTS SYS-3: the solution is unique).  Raises CyclicError if cyclic."""
    rho = ranks(game)
    if rho is None:
        raise CyclicError("successor graph (robot kernel K and the human variant's kernels) has a cycle; "
                          "use trace/solve_horizon/multistart instead")
    pi, Vr, U = _uniform(game), np.zeros(game.S), np.zeros(game.S)
    Q = np.zeros((game.S, game.A))
    for r in range(rho.max() + 1):
        layer = np.flatnonzero(rho == r)
        for s in layer:
            if not game.terminal[s]:
                Q[s] = game.gamma_r * game.K[s] @ Vr
                if not np.all(Q[s] < 0):
                    raise ValueError(f"state {s}: Q(s,.) = {Q[s]} is not negative (check data / positivity of U)")
                l = -game.beta * np.log(-Q[s])
                pi[s] = np.exp(l - lse(l))
        Ur, _ = game.human.evaluate(pi)           # Ve(s) for rank <= r depends only on pi at rank <= r (Local)
        if not np.all(np.isfinite(Ur[layer])) or np.any(Ur[layer] >= 0):
            raise ValueError(f"rank {r}: U = {Ur[layer]} is not negative (human values must be positive)")
        for s in layer:
            U[s] = Ur[s]
            Vr[s] = U[s] + pi[s] @ Q[s]
    z = np.log(-Q[game.nt]).ravel()
    return make_result(game, z, params_of(game), "acyclic", notes="exact backward induction; unique by SYS-3")


# ---------------------------------------------------------------- (b) finite horizon
def solve_horizon(game, T_max=3000, tol=1e-10, polish=True):
    """Unrolled T-step game, T = 1, 2, ...: layer 0 is terminal (pi uniform, Ve_0 = Phi pi_unif 0, Vr_0 = U_0), and
    Q_k = gamma_r K Vr_{k-1}, pi_k = powerlaw(Q_k), Ve_k = Phi pi_k Ve_{k-1}, U_k = Psi(Ve_k), Vr_k = U_k + pi_k.Q_k.
    Each layer is determined uniquely (acyclic).  Stops when pi_T satisfies the stationary system to `tol`."""
    h, p = game.human, params_of(game)
    pi = _uniform(game)
    Ve = h.phi(pi, h.zeros())
    Vr = h.U_of(Ve)
    if not np.all(Vr < 0):
        return make_result(game, z_from_pi(game, pi), p, "horizon", 0, False, "U_0 is not negative: cannot start")
    hist, pis = [], []
    z, res, T = None, np.inf, 0
    for T in range(1, T_max + 1):
        Q = game.gamma_r * game.K @ Vr
        if not np.all(Q[game.nt] < 0):
            return make_result(game, z if z is not None else z_from_pi(game, pi), p, "horizon", T, False,
                               f"Q not negative at T={T}")
        pi = _powerlaw(game, Q)
        Ve = h.phi(pi, Ve)
        U = h.U_of(Ve)
        if not np.all(U < 0):
            return make_result(game, np.log(-Q[game.nt]).ravel(), p, "horizon", T, False, f"U not negative at T={T}")
        Vr = U + (pi * Q).sum(1)
        z = np.log(-Q[game.nt]).ravel()
        res = float(np.abs(residual(game, z, p)).max())
        hist.append(res); pis.append(pi[game.nt])
        if res < tol:
            return make_result(game, z, p, "horizon", T, True, f"stationary residual < {tol:g} at horizon T={T}")
    note = f"no convergence in T_max={T_max}; final residual {res:.2e}"
    tail = np.array(hist[-50:])
    for per in range(1, 25):
        if len(pis) > 2 * per and np.abs(pis[-1] - pis[-1 - per]).max() < 1e-8 and np.abs(pis[-1] - pis[-2]).max() > 1e-6:
            note += f"; policies are periodic with period {per} (limit cycle, no stationary solution reached)"
            break
    else:
        note += "; residual " + ("still decreasing (slow convergence)" if tail[-1] < 0.99 * tail[0] else "stagnates/oscillates")
    if polish and res < 1e-3:
        z2, nr, it, ok = newton(game, z, p)
        if ok:
            return make_result(game, z2, p, "horizon", T, True, note + "; polished by Newton from the horizon iterate")
    return make_result(game, z, p, "horizon", T, False, note)


# ---------------------------------------------------------------- (c) continuation
_DEFAULT_START = {"beta": 0.0, "gamma_r": 1e-3, "gamma_h": 0.0}


def _target_of(game, param):
    if param == "gamma_h":
        g = game.human.gamma_h
        if np.ptp(g) > 0:
            raise ValueError("tracing in gamma_h needs equal gamma_h for all humans")
        return float(g[0])
    return float(getattr(game, param))


@dataclass
class Trace:
    param: str
    target: float
    lam: np.ndarray                 # parameter values along the path
    z: np.ndarray                   # (npts, n) log(-Q)
    crossings: list                 # Results at lam = target, in path order
    folds: list                     # dicts(lam, index): approximate fold locations (turning points in lam)
    sigma: np.ndarray               # smallest singular value of [Jz | Jmu] along the path
    status: str
    game: object = None

    @property
    def selected(self):
        """The solution at the target reached first when following the branch from the start (None if never reached)."""
        return self.crossings[0] if self.crossings else None


def trace(game, param="beta", start=None, target=None, lam_max=None, h0=0.1, hmax=1.0, hmin=1e-9, max_steps=4000,
          tol=1e-10):
    """Pseudo-arclength predictor-corrector continuation of the solution branch in `param`
    ("beta" from 0, "gamma_r" from ~1e-3 (traced in log gamma_r), "gamma_h" from 0), unknowns z = log(-Q).
    Starting solution: Newton from the policy generated by uniform pi at the start value (unique for beta = 0 [SYS-2];
    otherwise not guaranteed unique).  Follows the branch through folds and returns every crossing of `target`."""
    if param not in ("beta", "gamma_r", "gamma_h"):
        raise ValueError("param must be 'beta', 'gamma_r' or 'gamma_h'")
    L = _target_of(game, param) if target is None else float(target)
    lam0 = _DEFAULT_START[param] if start is None else float(start)
    if lam_max is None:
        lam_max = {"beta": 2 * L + 1, "gamma_r": max(L, 0.999), "gamma_h": max(L, 0.999)}[param]
    lo, hi = min(lam0, L), max(lam_max, L, lam0)
    to_mu, from_mu = (np.log, np.exp) if param == "gamma_r" else (lambda x: x, lambda x: x)
    dlam = (lambda mu: np.exp(mu)) if param == "gamma_r" else (lambda mu: 1.0)
    base = params_of(game)
    P = lambda lam: base._replace(**{{"beta": "beta", "gamma_r": "gamma_r", "gamma_h": "gh"}[param]: lam})

    def FJ(y):
        lam = from_mu(y[-1])
        Jz, Jl = jacobian(game, y[:-1], P(lam), param)
        return residual(game, y[:-1], P(lam)), np.column_stack([Jz, Jl * dlam(y[-1])])

    def tangent(A, prev):
        t = np.linalg.svd(A)[2][-1]
        return t if t @ prev >= 0 else -t

    # start point
    pi0 = _uniform(game)
    z0 = z_from_pi(game, pi0, lam0 if param == "gamma_h" else None) if param == "gamma_h" else \
        z_from_pi(game.with_params(**{param: lam0}), pi0)
    z0, nr, _, ok = newton(game, z0, P(lam0))
    if not ok:
        raise RuntimeError(f"no starting solution at {param} = {lam0} (Newton residual {nr:.2e})")
    y = np.append(z0, to_mu(lam0))
    R, A = FJ(y)
    dirn = np.zeros(len(y)); dirn[-1] = np.sign(to_mu(L) - to_mu(lam0)) or 1.0
    t = tangent(A, dirn)
    lams, zs, sig, crossings, folds = [lam0], [z0], [np.linalg.svd(A, compute_uv=False)[-1]], [], []
    if lam0 == L:
        crossings.append(make_result(game, z0, P(lam0), f"trace-{param}", 0))
    h, status = h0, "max_steps reached"
    for step in range(max_steps):
        for _ in range(60):                          # step-size loop
            yc, ok = y + h * t, False
            for k in range(12):
                try:
                    R, A = FJ(yc)
                    d = np.linalg.solve(np.vstack([A, t]), -np.append(R, t @ (yc - y) - h))
                except (np.linalg.LinAlgError, ValueError):
                    break
                if not np.all(np.isfinite(d)):
                    break
                yc = yc + d
                if np.abs(d).max() < 1e-11 and np.abs(R).max() < tol:
                    ok = True
                    break
            if ok:
                Rn, An = FJ(yc)
                ok = np.isfinite(Rn).all() and np.abs(Rn).max() < 1e-9 and np.linalg.norm(yc - y - h * t) < 0.5 * h + 1e-9
            if ok:
                t2 = tangent(An, t)
                ok = t @ t2 > 0.9
                fold = t[-1] * t2[-1] < 0
                if ok and fold and abs(h) > 0.02:
                    ok = False                           # resolve folds with small steps
            if ok:
                break
            h *= 0.5
            if h < hmin:
                status = f"step collapse at {param} = {from_mu(y[-1]):.6g} (singular point / branch point?)"
                break
        else:
            status = "step-size loop failed"
        if not ok:
            break
        lam_a, lam_b = from_mu(y[-1]), from_mu(yc[-1])
        if fold:
            s = t[-1] / (t[-1] - t2[-1])
            folds.append(dict(lam=float(lam_a + s * (lam_b - lam_a)), index=len(lams)))
        if (lam_a - L) * (lam_b - L) < 0 or lam_b == L:
            w = (L - lam_a) / (lam_b - lam_a)
            zi = y[:-1] + w * (yc[:-1] - y[:-1])
            zc, nr, it, ok2 = newton(game, zi, P(L))
            note = "" if ok2 and np.abs(zc - zi).max() < 1.0 else "refinement failed or jumped; unrefined interpolant"
            crossings.append(make_result(game, zc if note == "" else zi, P(L), f"trace-{param}", step, notes=note))
        y, t = yc, t2
        lams.append(lam_b); zs.append(y[:-1].copy()); sig.append(np.linalg.svd(An, compute_uv=False)[-1])
        h = min(h * 1.6 if k <= 3 else h, hmax)
        if lam_b > hi or lam_b < lo - 1e-12:
            status = f"left parameter range [{lo:g}, {hi:g}]"
            break
    return Trace(param, L, np.array(lams), np.array(zs), crossings, folds, np.array(sig), status, game)


# ---------------------------------------------------------------- (d) multistart
def _distinct(sols, z, tol=1e-6):
    return all(np.abs(s.z - z).max() > tol for s in sols)


def multistart(game, n=60, seed=0, tol=1e-11):
    """Random policies (logit scales 0.5..40, so near-deterministic ones occur) -> z_from_pi -> Newton, with
    scipy.optimize.root (hybr, exact Jacobian) as fallback; returns the distinct solutions (merged at |dz| > 1e-6)."""
    rng = np.random.default_rng(seed)
    p = params_of(game)
    sols = []
    nn = len(game.nt)
    for i in range(n):
        sc = rng.choice([0.5, 2.0, 8.0, 20.0, 40.0])
        l = rng.normal(0, sc, size=(nn, game.A))
        pi = _uniform(game)
        pi[game.nt] = np.exp(l - lse(l)[:, None])
        try:
            z = z_from_pi(game, pi)
        except Exception:
            continue
        z, nr, it, ok = newton(game, z, p, tol=tol)
        if not ok:
            sol = root(lambda x: np.nan_to_num(residual(game, x, p), nan=1e6, posinf=1e6, neginf=-1e6), z,
                       jac=lambda x: jacobian(game, x, p), method="hybr", tol=1e-13)
            z, ok = sol.x, bool(sol.success and np.abs(residual(game, sol.x, p)).max() < 1e-9)
        if ok and _distinct(sols, z):
            sols.append(make_result(game, z, p, "multistart", i))
    return sols


# ---------------------------------------------------------------- (e) front end
@dataclass
class Solutions:
    solutions: list                 # distinct Results; each has .found_by (list of method labels)
    warnings: list = field(default_factory=list)
    notes: list = field(default_factory=list)

    def summary(self):
        out = [f"{len(self.solutions)} distinct solution(s)"]
        for i, s in enumerate(self.solutions):
            out.append(f"#{i} found by {s.found_by}: residual {s.residual:.1e}\n  pi=" + np.array2string(s.pi, precision=6).replace("\n", ""))
        out += ["WARNING: " + w for w in self.warnings] + ["note: " + n for n in self.notes]
        return "\n".join(out)


def _add(sols, r, label):
    if not r.success:
        return
    for s in sols:
        if np.abs(s.z - r.z).max() < 1e-6:
            if label not in s.found_by:
                s.found_by.append(label)
            return
    r.found_by = [label]
    sols.append(r)


def solve(game, multistart_n=0, horizon=True, traces=("beta",), seed=0):
    """Front end.  Acyclic: exact (unique, SYS-3).  Otherwise: beta-trace from 0 (all crossings of the target),
    finite-horizon unrolling, optional multistart; distinct solutions are merged and labelled by the methods that found them."""
    sols, notes = Solutions([]), []
    if ranks(game) is not None:
        _add(sols.solutions, solve_acyclic(game), "acyclic")
        sols.notes.append("acyclic: unique solution [SYS-3]")
        return sols
    sols.notes.append("cyclic: uniqueness not guaranteed" + (" (beta = 0: unique [SYS-2])" if game.beta == 0 else ""))
    for prm in traces:
        try:
            tr = trace(game, prm)
            for r in tr.crossings:
                _add(sols.solutions, r, f"trace-{prm}")
            sols.notes.append(f"trace-{prm}: {len(tr.crossings)} crossing(s), {len(tr.folds)} fold(s), {tr.status}")
            if not tr.crossings:
                sols.warnings.append(f"trace-{prm} did not reach the target ({tr.status})")
        except Exception as e:
            sols.warnings.append(f"trace-{prm} failed: {e}")
    if horizon:
        r = solve_horizon(game)
        _add(sols.solutions, r, "horizon")
        sols.notes.append(f"horizon: {r.notes}")
        if not r.success:
            sols.warnings.append("finite-horizon iteration did not converge (see notes)")
    if multistart_n:
        for r in multistart(game, multistart_n, seed):
            _add(sols.solutions, r, "multistart")
    if len(sols.solutions) > 1:
        sols.warnings.append(f"{len(sols.solutions)} distinct solutions: the system is not unique here [SYS-6]; "
                             "which one a method returns is a property of that method, not of the problem")
    if not sols.solutions:
        sols.warnings.append("no solution found (existence is open [SYS-4])")
    return sols
