"""Variant 3 (owner's 'trajectory-goal' power, no goal dimension):  X_h(s) = 1 + sum_s' max_ah Pbar(h,s,ah,s')^zeta X_h(s')."""
import numpy as np
from dataclasses import dataclass


@dataclass
class Game3:
    T: np.ndarray    # (H,S,Ai,B,A,S), rows sum <= 1 (termination)
    q: np.ndarray    # (H,S,B)
    zeta: float; xi: float; eta: float; gr: float
    rho_fail = 0     # count of pi for which spectral radius of M >= 1 (X infinite)
    nev = 0
    @property
    def dims(self): return self.T.shape[1], self.T.shape[4], self.T.shape[0], 1
    @property
    def K(self):  # robot kernel: average over h and a_h (uniform), b (q)  [assumption: no p in this variant]
        return np.einsum('hsb,hsibat->sat', self.q, self.T) / (self.T.shape[0] * self.T.shape[2])
    def human(self, pi, jac=False):
        S, A, H, _ = self.dims
        Tb = np.einsum('hsb,hsibat->hsiat', self.q, self.T)
        Pb = np.einsum('sa,hsiat->hsit', pi, Tb); Pz = Pb ** self.zeta
        im = Pz.argmax(2); M = np.take_along_axis(Pz, im[:, :, None, :], 2)[:, :, 0, :]    # (H,S,S)
        Game3.nev += 1
        if max(np.abs(np.linalg.eigvals(M)).max(axis=-1) if M.ndim == 3 else [0]) >= 1:
            Game3.rho_fail += 1; n = np.full(S, np.nan)
            return (None, np.full((H, S), np.nan), n) + ((np.full((S, S * A), np.nan),) if jac else ())
        Minv = np.linalg.inv(np.eye(S) - M); X = np.einsum("hst,t->hs", Minv, np.ones(S))
        T = (X ** -self.xi).sum(0); c = T ** self.eta
        if not jac: return None, X, c
        Ts = np.take_along_axis(Tb, im[:, :, None, None, :], 2)[:, :, 0]                  # (H,S,A,S) best a_h
        Pbs = np.take_along_axis(Pb, im[:, :, None, :], 2)[:, :, 0, :]
        dM = self.zeta * Pbs[:, :, None, :] ** (self.zeta - 1) * Ts                       # (H,S,A,S)
        dMX = np.einsum('hsat,ht->hsa', dM, X)
        dX = np.einsum('hos,hsa->hosa', Minv, dMX)
        dc = (self.eta * T ** (self.eta - 1))[:, None, None] * np.einsum('ho,hosa->osa', -self.xi * X ** (-self.xi - 1), dX)
        return None, X, c, dc.reshape(S, S * A)


def rand_game3(rng, kind=None):
    S = int(rng.choice([2, 3, 4])); A = int(rng.choice([2, 3])); H = int(rng.choice([1, 2])); B = int(rng.choice([1, 2])); Ai = 2
    kind = kind or rng.choice(['dense', 'det', 'bad']); shape = (H, S, Ai, B, A)
    if kind == 'dense': T = rng.dirichlet(np.ones(S) * rng.choice([0.3, 1.0]), size=shape)
    else:
        nxt = rng.integers(0, S, size=shape)
        if kind == 'bad': nxt[:, 0] = 0
        T = np.eye(S)[nxt]
    T = T * rng.uniform(0.3, 1.0, size=shape + (1,))
    return Game3(T, rng.dirichlet(np.ones(B), size=(H, S)), *rng.uniform(1, 3, 3), rng.uniform(0.5, 0.99))
