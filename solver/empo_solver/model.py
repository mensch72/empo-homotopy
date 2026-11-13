"""Tabular data model: Game (robot kernel + parameters) and the three human-value variants.

Each variant provides  phi(pi, V, gh)  (one application of the evaluation operator Phi, V of shape (H,G,S)),
evaluate(pi, gh) -> (U, aux)  (Ve = Phi pi Ve solved, U = Psi(Ve) < 0) and support() (successor graph).
All code is complex-step safe (pi, gh may be complex) so that Jacobians are exact to machine precision.
"""
from dataclasses import dataclass, replace
import numpy as np


class ValidationError(ValueError):
    pass


def _arr(x, name, shape=None, nonneg=False):
    a = np.asarray(x, dtype=float)
    if shape is not None and a.shape != tuple(shape):
        raise ValidationError(f"{name}: expected shape {tuple(shape)}, got {a.shape}")
    if not np.all(np.isfinite(a)):
        raise ValidationError(f"{name}: contains NaN or inf")
    if nonneg and np.any(a < 0):
        raise ValidationError(f"{name}: entries must be nonnegative (min {a.min():.3g})")
    return a


def _kernel(x, name, shape):
    a = _arr(x, name, shape, nonneg=True)
    if a.sum(-1).max() > 1 + 1e-9:
        raise ValidationError(f"{name}: row sums must be <= 1 (max {a.sum(-1).max():.12g})")
    return a


def _pw(x, e):
    """x**e for x >= 0 (complex-safe; 0 stays 0 for e > 0)."""
    if e < 0:
        return x ** e
    ok = x.real > 0
    return np.where(ok, np.where(ok, x, 1.0) ** e, 0.0)


def _check_scalars(v, **kw):
    for k, (lo, hi) in kw.items():
        val = getattr(v, k)
        if not (np.all(np.isfinite(val)) and np.all(np.asarray(val) >= lo) and np.all(np.asarray(val) < hi)):
            raise ValidationError(f"{k} must lie in [{lo}, {hi}), got {val}")


class Variant:
    """Common part: Psi (eqs. (7)-(8)) and the fixed-point solve wrapper."""
    def _gh(self, gh):
        g = np.broadcast_to(np.asarray(self.gamma_h if gh is None else gh), (self.H,))
        return g[:, None, None]

    def X(self, Ve):
        return (Ve ** self.zeta).sum(1)           # (H,S); trajectory overrides

    def U_of(self, Ve):
        if np.any(Ve.real <= 0):
            return np.full(Ve.shape[-1], np.nan)
        X = self.X(Ve)
        return -((X ** -self.xi).sum(0)) ** self.eta

    def zeros(self):
        return np.zeros((self.H, self.G, self.S))

    def _bind_common(self, S, A):
        if self.S != S:
            raise ValidationError(f"{type(self).__name__}: has {self.S} states but robot kernel K has {S}")
        if self.A != A:
            raise ValidationError(f"{type(self).__name__}: has {self.A} robot actions but robot kernel K has {A}")


@dataclass
class Linear(Variant):
    """Linear (6): Ve(h,g,s) = sum_a pi(s,a) [ r(h,g,s,a) + gamma_h sum_s' Kh(h,g,s,a,s') Ve(h,g,s') ]."""
    Kh: np.ndarray
    r: np.ndarray
    gamma_h: object = 0.9
    zeta: float = 1.0
    xi: float = 1.0
    eta: float = 1.0

    def __post_init__(self):
        Kh = np.asarray(self.Kh, dtype=float)
        if Kh.ndim != 5:
            raise ValidationError(f"Linear.Kh: expected shape (H,G,S,A,S), got {Kh.shape}")
        self.H, self.G, self.S, self.A, _ = Kh.shape
        self.Kh = _kernel(Kh, "Linear.Kh", Kh.shape)
        self.r = _arr(self.r, "Linear.r", Kh.shape[:4])
        self.gamma_h = _arr(np.broadcast_to(self.gamma_h, (self.H,)), "Linear.gamma_h")
        if np.any(self.gamma_h < 0) or np.any(self.gamma_h >= 1):
            raise ValidationError("Linear.gamma_h must lie in [0,1) (SYS-L)")
        if min(self.zeta, self.xi, self.eta) <= 0:
            raise ValidationError("zeta, xi, eta must be positive")

    def bind(self, S, A): self._bind_common(S, A)
    def support(self): return self.Kh.any(axis=(0, 1, 3))

    def phi(self, pi, V, gh=None):
        Pk = np.einsum('sa,hgsat->hgst', pi, self.Kh)
        return np.einsum('sa,hgsa->hgs', pi, self.r) + self._gh(gh) * np.einsum('hgst,hgt->hgs', Pk, V)

    def evaluate(self, pi, gh=None):
        Pk = self._gh(gh)[..., None] * np.einsum('sa,hgsat->hgst', pi, self.Kh)
        rp = np.einsum('sa,hgsa->hgs', pi, self.r)
        Ve = np.linalg.solve(np.eye(self.S) - Pk, rp[..., None])[..., 0]
        return self.U_of(Ve), dict(Ve=Ve, X=self.X(Ve) if not np.any(Ve.real <= 0) else None)


@dataclass
class PowerMean(Variant):
    """Power-mean (6'): data as in numerics/cyclic/system.py.
    T[h,g,s,i,b,a,s'] (i: own action, b: folded other-human actions, a: robot action), q[h,s,b], p[h,g,s,i], u[h,g,s']."""
    T: np.ndarray
    q: np.ndarray
    p: np.ndarray
    u: np.ndarray
    kappa: float = 1.0
    theta: float = 1.0
    gamma_h: object = 0.9
    zeta: float = 1.0
    xi: float = 1.0
    eta: float = 1.0
    tol: float = 1e-14
    maxit: int = 100000

    def __post_init__(self):
        T = np.asarray(self.T, dtype=float)
        if T.ndim != 7:
            raise ValidationError(f"PowerMean.T: expected shape (H,G,S,Ai,B,A,S), got {T.shape}")
        H, G, S, Ai, B, A, _ = T.shape
        self.H, self.G, self.S, self.A = H, G, S, A
        self.T = _kernel(T, "PowerMean.T", T.shape)
        self.q = _arr(self.q, "PowerMean.q", (H, S, B), True)
        self.p = _arr(self.p, "PowerMean.p", (H, G, S, Ai), True)
        self.u = _arr(self.u, "PowerMean.u", (H, G, S), True)
        for nm, arr in (("q", self.q), ("p", self.p)):
            if not np.allclose(arr.sum(-1), 1):
                raise ValidationError(f"PowerMean.{nm}: must sum to 1 over its last axis")
        self.gamma_h = _arr(np.broadcast_to(self.gamma_h, (H,)), "PowerMean.gamma_h")
        if np.any(self.gamma_h < 0) or np.any(self.gamma_h >= 1):
            raise ValidationError("PowerMean.gamma_h must lie in [0,1)")
        if self.kappa == 0 or self.theta == 0 or self.kappa > 1 or self.theta > 1:
            raise ValidationError("kappa, theta must be nonzero and <= 1")
        if min(self.zeta, self.xi, self.eta) <= 0:
            raise ValidationError("zeta, xi, eta must be positive")

    def bind(self, S, A): self._bind_common(S, A)
    def support(self): return self.T.any(axis=(0, 1, 3, 4, 5))

    def default_robot_kernel(self):
        """Robot kernel K = average of T over h,g (uniform), a_h (p), b (q) (the reading used in numerics/cyclic)."""
        return np.einsum('hgsi,hsb,hgsibat->sat', self.p, self.q, self.T) / (self.H * self.G)

    def phi(self, pi, V, gh=None):
        k, th = self.kappa, self.theta
        Y = np.einsum('hgsibat,hgt->hgsiba', self.T, self.u + self._gh(gh) * V)
        Z = np.einsum('sa,hgsiba->hgsib', pi, _pw(Y, k))
        Sa = np.einsum('hsb,hgsib->hgsi', self.q, _pw(Z, th / k))
        return np.einsum('hgsi,hgsi->hgs', self.p, _pw(Sa, 1 / th))

    def evaluate(self, pi, gh=None):
        V = self.zeros() + 0 * pi.flat[0]
        for _ in range(self.maxit):
            V2 = self.phi(pi, V, gh)
            dr = np.abs((V2 - V).real).max()
            di = np.abs((V2 - V).imag).max() / (np.abs(V2.imag).max() + 1e-300)
            V = V2
            if not np.isfinite(dr):
                break
            if dr < self.tol and (di < 1e-9 or np.abs(V2.imag).max() == 0):
                return self.U_of(V), dict(Ve=V, X=self.X(V))
        return np.full(self.S, np.nan), dict(Ve=V, X=None, note="Ve fixed-point iteration did not converge")


@dataclass
class Trajectory(Variant):
    """Discounted trajectory goals (7T): X_h(s) = 1 + gamma_h sum_s' max_{a_h} P(s'|s,a_h,pi)^zeta X_h(s'),
    P(s'|s,a_h,pi) = sum_a pi(s,a) Pbar[h,s,a_h,a,s'].  U = -(sum_h X_h^-xi)^eta (no goal dimension, G = 1)."""
    Pbar: np.ndarray
    gamma_h: object = 0.9
    zeta: float = 1.0
    xi: float = 1.0
    eta: float = 1.0

    def __post_init__(self):
        P = np.asarray(self.Pbar, dtype=float)
        if P.ndim != 5:
            raise ValidationError(f"Trajectory.Pbar: expected shape (H,S,Ai,A,S), got {P.shape}")
        self.H, self.S, _, self.A, _ = P.shape
        self.G = 1
        self.Pbar = _kernel(P, "Trajectory.Pbar", P.shape)
        self.gamma_h = _arr(np.broadcast_to(self.gamma_h, (self.H,)), "Trajectory.gamma_h")
        if np.any(self.gamma_h < 0):
            raise ValidationError("Trajectory.gamma_h must be >= 0")
        if min(self.zeta, self.xi, self.eta) <= 0:
            raise ValidationError("zeta, xi, eta must be positive")

    def bind(self, S, A): self._bind_common(S, A)
    def support(self): return self.Pbar.any(axis=(0, 2, 3))
    def X(self, Ve): return Ve[:, 0, :]

    def _M(self, pi):
        P = np.einsum('sa,hsiat->hsit', pi, self.Pbar)
        Pz = _pw(P, self.zeta)
        im = Pz.real.argmax(2)
        return np.take_along_axis(Pz, im[:, :, None, :], 2)[:, :, 0, :]      # (H,S,S)

    def phi(self, pi, V, gh=None):
        M = self._M(pi)
        return (1 + self._gh(gh)[:, 0, :] * np.einsum('hst,ht->hs', M, V[:, 0, :]))[:, None, :]

    def evaluate(self, pi, gh=None):
        gM = self._gh(gh) * self._M(pi)
        if np.max(np.abs(np.linalg.eigvals(gM.real))) >= 1:
            return np.full(self.S, np.nan), dict(Ve=None, X=None, note="spectral radius of gamma_h M >= 1")
        X = np.linalg.solve(np.eye(self.S) - gM, np.ones((self.H, self.S, 1)))[..., 0]
        return self.U_of(X[:, None, :]), dict(Ve=X[:, None, :], X=X)


@dataclass
class Game:
    """Robot kernel K[s,a,s'] (rows sum <= 1; all-zero rows for all actions = terminal state), a human-value
    variant, and the parameters beta >= 0, gamma_r > 0."""
    K: np.ndarray
    human: Variant
    beta: float = 1.0
    gamma_r: float = 0.9
    name: str = ""

    def __post_init__(self):
        K = np.asarray(self.K, dtype=float)
        if K.ndim != 3 or K.shape[0] != K.shape[2]:
            raise ValidationError(f"K: expected shape (S,A,S), got {K.shape}")
        self.K = _kernel(K, "K", K.shape)
        S, A, _ = K.shape
        if A < 1:
            raise ValidationError("K: need at least one action")
        self.S, self.A = S, A
        mass = self.K.sum(-1)
        self.terminal = ~mass.any(axis=1)
        self.nt = np.flatnonzero(~self.terminal)
        for s in self.nt:
            if np.any(mass[s] <= 0):
                raise ValidationError(f"K: non-terminal state {s} has an action with zero successor mass "
                                      f"(row sums {mass[s]}); a solution would need Q = 0 there")
        if not (np.isfinite(self.beta) and self.beta >= 0):
            raise ValidationError(f"beta must be >= 0, got {self.beta}")
        if not (np.isfinite(self.gamma_r) and self.gamma_r > 0):
            raise ValidationError(f"gamma_r must be > 0 (a solution forces it), got {self.gamma_r}")
        self.human.bind(S, A)

    def with_params(self, **kw):
        if "gamma_h" in kw:
            h = replace(self.human, gamma_h=kw.pop("gamma_h"))
            return replace(self, human=h, **kw)
        return replace(self, **kw)
