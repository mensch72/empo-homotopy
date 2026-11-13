"""Abstract target system of notes/STATEMENTS.md s0.  Unknown: z = log x, x = -Q (S*A).  pi = softmax(-beta*z)."""
import numpy as np
from dataclasses import dataclass


@dataclass
class Game:
    T: np.ndarray    # (H,G,S,Ai,B,A,S) kernel, rows sum <= 1
    q: np.ndarray    # (H,S,B) weights of folded other-human actions
    p: np.ndarray    # (H,G,S,Ai) human policy
    u: np.ndarray    # (H,G,S) reward U_h(s',g) (+eps already added)
    zeta: float; xi: float; eta: float; gh: float; gr: float; kappa: float = 1.0; theta: float = 1.0
    ncv = 0   # counters: Ve iterations not converged
    @property
    def dims(self): return self.T.shape[2], self.T.shape[5], self.T.shape[0], self.T.shape[1]
    @property
    def K(self):  # robot kernel: average of T over h,g (uniform), a_h (p), b (q)
        return np.einsum('hgsi,hsb,hgsibat->sat', self.p, self.q, self.T) / (self.T.shape[0] * self.T.shape[1])
    def todict(self):
        d = {k: getattr(self, k) for k in ('zeta', 'xi', 'eta', 'gh', 'gr', 'kappa', 'theta')}
        d.update({k: getattr(self, k).tolist() for k in ('T', 'q', 'p', 'u')}); return d
    @staticmethod
    def fromdict(d):
        return Game(*(np.array(d[k]) for k in ('T', 'q', 'p', 'u')), *(d[k] for k in ('zeta', 'xi', 'eta', 'gh', 'gr', 'kappa', 'theta')))


def softmax_pi(g, z, beta):
    S, A = g.dims[:2]
    l = -beta * z.reshape(S, A); l = l - l.max(1, keepdims=True)
    p = np.exp(l); return p / p.sum(1, keepdims=True)


def _F(g, pi, V, deriv=False):
    """Ve-operator F(V; pi) = RHS of the nonlinear human equation (all (h,g,s) at once)."""
    k, th = g.kappa, g.theta
    Y = np.einsum('hgsibat,hgt->hgsiba', g.T, g.u + g.gh * V)
    Yk = Y ** k; Z = np.einsum('sa,hgsiba->hgsib', pi, Yk); Wb = Z ** (th / k)
    Sa = np.einsum('hsb,hgsib->hgsi', g.q, Wb); F = np.einsum('hgsi,hgsi->hgs', g.p, Sa ** (1 / th))
    if not deriv: return F
    cA = g.p * Sa ** (1 / th - 1) / th
    cB = cA[..., None] * g.q[:, None, :, None, :] * (th / k) * Z ** (th / k - 1)
    Fpi = np.einsum('hgsib,hgsiba->hgsa', cB, Yk)
    FV = g.gh * k * np.einsum('hgsib,sa,hgsiba,hgsibat->hgst', cB, pi, Y ** (k - 1), g.T)
    return F, Fpi, FV


def solve_ve(g, pi, V0=None, fp=8, tol=1e-14):
    """Fixed-point iterations from V0 (default 0) then Newton; counts non-convergence in Game.ncv."""
    V = np.zeros(g.u.shape) if V0 is None else V0.copy(); n = g.u.shape[2]
    for _ in range(fp): V = _F(g, pi, V)
    for _ in range(30):
        F, _, FV = _F(g, pi, V, True); R = V - F
        if np.abs(R).max() < tol: return V
        D = np.linalg.solve(np.eye(n) - FV, R[..., None])[..., 0]; V = V - D
    for _ in range(5000):
        V = _F(g, pi, V)
        if np.abs(V - _F(g, pi, V)).max() < 1e-12: return V
    Game.ncv += 1; return V


def human(g, pi, jac=False):
    """pi (S,A) -> Ve (H,G,S), X (H,S), c = -U (S,) [and dc/dpi as (S, S*A)]."""
    S, A, H, G = g.dims
    Ve = solve_ve(g, pi)
    X = (np.maximum(Ve, 0) ** g.zeta).sum(1)
    T = (X ** -g.xi).sum(0); c = T ** g.eta
    if not jac: return Ve, X, c
    _, Fpi, FV = _F(g, pi, Ve, True)
    Minv = np.linalg.inv(np.eye(S) - FV)
    dVe = np.einsum('hgos,hgsa->hgosa', Minv, Fpi)
    dX = np.einsum('hgo,hgosa->hosa', g.zeta * np.maximum(Ve, 0) ** (g.zeta - 1), dVe)
    dc = (g.eta * T ** (g.eta - 1))[:, None, None] * np.einsum('ho,hosa->osa', -g.xi * X ** (-g.xi - 1), dX)
    return Ve, X, c, dc.reshape(S, S * A)


def dpi_dx(g, pi, x, beta):
    S, A = g.dims[:2]; D = np.zeros((S * A, S * A)); xs = x.reshape(S, A)
    for s in range(S):
        p = pi[s]; D[s*A:(s+1)*A, s*A:(s+1)*A] = -beta * (np.diag(p) - np.outer(p, p)) / xs[s][None, :]
    return D


def resid(g, z, beta, jac=False):
    """R = 1 - gr*(K (c+w))/x  (zero iff x = gr K (c + w_beta(x)) with c = -U(pi(x)))."""
    S, A = g.dims[:2]; x = np.exp(z); xs = x.reshape(S, A)
    pi = softmax_pi(g, z, beta)
    with np.errstate(all='ignore'):
        out = human(g, pi, jac)
        c = out[2]; w = (pi * xs).sum(1)
        N = g.gr * g.K.reshape(S * A, S) @ (c + w); R = 1 - N / x
        if not jac: return R
        dc = out[3]; Dp = dpi_dx(g, pi, x, beta)
        dw = np.zeros((S, S * A))
        for s in range(S):
            dw[s, s*A:(s+1)*A] = pi[s] * (1 - beta + beta * w[s] / xs[s])
        dN = g.gr * g.K.reshape(S * A, S) @ (dc @ Dp + dw)
        J = -dN * x[None, :] / x[:, None] + np.diag(N / x)
    return R, J


def newton(g, z, beta, tol=1e-12, maxit=80):
    for _ in range(maxit):
        try: R, J = resid(g, z, beta, True)
        except np.linalg.LinAlgError: return z, np.inf
        nr = np.abs(R).max()
        if not np.isfinite(nr): return z, np.inf
        if nr < tol: return z, nr
        try: d = np.linalg.solve(J, -R)
        except np.linalg.LinAlgError: return z, nr
        m = np.abs(d).max()
        if m > 3: d *= 3 / m
        t = 1.0
        while t > 1e-4:
            with np.errstate(all='ignore'): nr2 = np.abs(resid(g, z + t * d, beta)).max()
            if np.isfinite(nr2) and nr2 < (1 - 1e-4 * t) * nr: break
            t /= 2
        z = z + t * d
    R = resid(g, z, beta); return z, np.abs(R).max()


def x_given_c(g, c, beta, x0=None, iters=60, damp=0.5):
    """Solve x = gr K (c + w_beta(x)) by damped iteration (the 'given U' robot problem)."""
    S, A = g.dims[:2]; Km = g.K.reshape(S * A, S)
    x = g.gr * Km @ c / (1 - g.gr) if x0 is None else x0.copy()
    for _ in range(iters):
        p = softmax_pi(g, np.log(x), beta); w = (p * x.reshape(S, A)).sum(1)
        x = (1 - damp) * x + damp * g.gr * Km @ (c + w)
    return x


def phi(g, pi, beta, x0=None):
    """fixed-point map pi -> normalise(x(U(pi))^-beta)."""
    c = human(g, pi)[2]; x = x_given_c(g, c, beta, x0)
    return softmax_pi(g, np.log(x), beta), x


def phi_jac_rho(g, z, beta):
    """spectral radius of d Phi/d pi at a solution (implicit differentiation of x(c))."""
    S, A = g.dims[:2]; x = np.exp(z); pi = softmax_pi(g, z, beta)
    _, _, c, dc = human(g, pi, True); Km = g.K.reshape(S * A, S)
    xs = x.reshape(S, A); w = (pi * xs).sum(1)
    dw = np.zeros((S, S * A))
    for s in range(S): dw[s, s*A:(s+1)*A] = pi[s] * (1 - beta + beta * w[s] / xs[s])
    dxdc = np.linalg.solve(np.eye(S * A) - g.gr * Km @ dw, g.gr * Km)   # (SA,S)
    Jf = dpi_dx(g, pi, x, beta) @ dxdc @ dc                              # (SA,SA)
    return np.abs(np.linalg.eigvals(Jf)).max()


def verify(g, z, beta):
    """Independent check (loops, plain iteration to 1e-15) of all solution conditions of s0 for pi, Q = -x."""
    S, A, H, G = g.dims; Ai, B = g.T.shape[3], g.T.shape[4]; x = np.exp(z).reshape(S, A); Q = -x
    pi = x ** -beta; pi /= pi.sum(1, keepdims=True)
    def F(V):
        o = np.zeros_like(V)
        for h in range(H):
            for k in range(G):
                for s in range(S):
                    for i in range(Ai):
                        t = 0.0
                        for b in range(B):
                            zz = sum(pi[s, a] * sum(g.T[h, k, s, i, b, a, u2] * (g.u[h, k, u2] + g.gh * V[h, k, u2]) for u2 in range(S)) ** g.kappa for a in range(A))
                            t += g.q[h, s, b] * zz ** (g.theta / g.kappa)
                        o[h, k, s] += g.p[h, k, s, i] * t ** (1 / g.theta)
        return o
    Ve = np.zeros((H, G, S)); res = 1
    for _ in range(100000):
        V2 = F(Ve); res = np.abs(V2 - Ve).max(); Ve = V2
        if res < 1e-15: break
    X = (Ve ** g.zeta).sum(1); U = -((X ** -g.xi).sum(0)) ** g.eta
    Vr = U + (pi * Q).sum(1); Q2 = g.gr * g.K @ Vr
    return dict(maxQ=Q.max(), minVe=Ve.min(), minX=X.min(), simplex=abs(pi.sum(1) - 1).max(), Qres=np.abs(Q - Q2).max() / np.abs(Q).max(),
                pires=np.abs(pi - softmax_pi(g, z, beta).reshape(S, A)).max(), vefp=res)
