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
    def todict(self): return dict(T=self.T.tolist(), q=self.q.tolist(), zeta=self.zeta, xi=self.xi, eta=self.eta, gr=self.gr)
    @staticmethod
    def fromdict(d): return Game3(np.array(d['T']), np.array(d['q']), d['zeta'], d['xi'], d['eta'], d['gr'])
    def human(self, pi, jac=False):
        S, A, H, _ = self.dims
        Tb = np.einsum('hsb,hsibat->hsiat', self.q, self.T)
        Pb = np.einsum('sa,hsiat->hsit', pi, Tb); Pz = Pb ** self.zeta
        im = Pz.argmax(2); M = np.take_along_axis(Pz, im[:, :, None, :], 2)[:, :, 0, :]    # (H,S,S)
        Game3.nev += 1
        if (not np.all(np.isfinite(M))) or max(np.abs(np.linalg.eigvals(M)).max(axis=-1) if M.ndim == 3 else [0]) >= 1:
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


def _verify3(g, z, beta):
    S, A, H, _ = g.dims; x = np.exp(z).reshape(S, A); Q = -x; pi = x ** -beta; pi /= pi.sum(1, keepdims=True)
    X = np.ones((H, S))
    for _ in range(200000):
        X2 = np.ones((H, S))
        for h in range(H):
            for s in range(S):
                for t in range(S):
                    X2[h, s] += max(sum(pi[s, a] * sum(g.q[h, s, b] * g.T[h, s, i, b, a, t] for b in range(g.T.shape[3])) for a in range(A)) ** g.zeta for i in range(g.T.shape[2])) * X[h, t]
        d = np.abs(X2 - X).max(); X = X2
        if d < 1e-14: break
    U = -((X ** -g.xi).sum(0)) ** g.eta; Vr = U + (pi * Q).sum(1); Q2 = g.gr * g.K @ Vr
    return dict(maxQ=Q.max(), minVe=np.nan, minX=X.min(), simplex=abs(pi.sum(1) - 1).max(), Qres=(np.abs(Q - Q2) / np.abs(Q)).max(), Xit=d)


Game3.verify3 = lambda self, z, beta: _verify3(self, z, beta)


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
