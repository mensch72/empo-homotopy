"""Tabular finite-horizon 'bus' toy model for the steering equations (STATEMENTS s0, eqs (1)-(5)).
Cycle graph with N nodes; state = (bus node, human nodes), layer t = 0..T (acyclic by time layering).
Bus moves {stay,+1,-1,+2}; humans {stay,+1,-1}.  Each agent slips (stays) w.p. `slip`; a human standing on the
bus node is carried to the bus's new node w.p. `carry`; a human moving INTO the bus node is blocked w.p. `block`.
Human h has a goal g (target node goals[h,g], prior[h,g]); U_h(s',g)=1[human h at goals[h,g] in s'].
Exogenous human policy pi_h(s,g): 0.1 each action + 0.7 on the distance-reducing one; the 'other humans' a_{-h}
are drawn from the goal-marginal pi_h(s)=E_g pi_h(s,g) (also used for E_{a_H} in (2)).
Equation (5) as printed (R1): V=(E_{a_h}(E_{a_-h}(E_{a_r~pi}(E_{s'}X)^kappa)^(theta/kappa))^(1/theta)), X=U+gamma_h V(s').
EPSILON FLOOR: V_h := eps + (expression), so V_h >= eps > 0 (assumption P); terminal layer has V_h = eps.
x_s = -U_r(s) = (1/xi)(E_h (E_g V_h^zeta)^(-xi))^eta   [= (3),(4): 2^(-xi P_h) = (E_g V^zeta)^(-xi)].
-Q_r(s,a) = x_s + d_a,  d_a = gamma_r sum_s' Tbar(s'|s,a) sum_a' pi(s')(a') (-Q_r(s',a')) >= 0   [(2), R2].
Local problem at s: pi = softmax(-beta log(x+d)) with x = u(pi)  [(1)]."""
import itertools
import numpy as np

class Local:
    """Local problem: d (A,), u: (K,A)->(K,) , bracket [lo,hi] containing range of u."""
    def __init__(s, d, u, lo, hi):
        s.d, s.u, s.lo, s.hi, s.n = np.asarray(d, float), u, lo, hi, 0
    def sigma(s, x, beta):
        x = np.atleast_1d(np.asarray(x, float))
        L = -beta * np.log(x[:, None] + s.d[None, :]); L -= L.max(1, keepdims=True)
        P = np.exp(L); return P / P.sum(1, keepdims=True)
    def phi(s, x, beta):
        x = np.atleast_1d(np.asarray(x, float)); s.n += len(x); return s.u(s.sigma(x, beta))
    def g(s, x, beta): return np.atleast_1d(x) - s.phi(x, beta)

MR, MH = [0, 1, -1, 2], [0, 1, -1]

class Bus:
    def __init__(s, nH=2, nG=3, T=3, zeta=1., xi=1.5, eta=1.2, kappa=1., theta=1., gh=.9, gr=.9, eps=.2,
                 slip=.2, carry=.7, block=.8, seed=0, N=4):
        s.__dict__.update(locals()); rng = np.random.default_rng(seed)
        s.goals = rng.integers(0, N, (nH, nG)); s.prior = rng.dirichlet(np.ones(nG), nH)
        s.shape = (N,) * (nH + 1); s.nS = N ** (nH + 1)
        s.pos = np.array(list(itertools.product(range(N), repeat=nH + 1)))  # row = state index (C order)
        s.init = int(np.ravel_multi_index((0,) + tuple(range(1, nH + 1)), s.shape))
        s.acts = list(itertools.product(range(3), repeat=nH)); s._c = {}
    def _own(s, h, m, b):
        t = (h + m) % s.N; p = 1 - s.slip
        if m != 0 and t == b: p *= 1 - s.block
        return {t: p, h: 1 - p} if t != h else {h: 1.}
    def _trans(s, si):
        if si in s._c: return s._c[si]
        b, *hs = s.pos[si]; T = np.zeros((4, len(s.acts), s.nS))
        Ph = np.zeros((s.nH, s.nG, 3))
        for i, h in enumerate(hs):
            for g in range(s.nG):
                dist = [min((h + m - s.goals[i, g]) % s.N, (s.goals[i, g] - h - m) % s.N) for m in MH]
                Ph[i, g] = .1; Ph[i, g, int(np.argmin(dist))] += .7
        for ar, mr in enumerate(MR):
            for bo, pb in (((b + mr) % s.N, 1 - s.slip), (b, s.slip)):
                for j, ah in enumerate(s.acts):
                    dists = []
                    for i, h in enumerate(hs):
                        own = s._own(h, MH[ah[i]], b)
                        if h == b:
                            d = {k: (1 - s.carry) * v for k, v in own.items()}; d[bo] = d.get(bo, 0) + s.carry
                        else: d = own
                        dists.append(d)
                    for combo in itertools.product(*[list(d.items()) for d in dists]):
                        p = pb
                        for _, q in combo: p *= q
                        T[ar, j, np.ravel_multi_index((bo,) + tuple(k for k, _ in combo), s.shape)] += p
        pm = np.einsum('hg,hga->ha', s.prior, Ph)
        pj = np.array([np.prod([pm[i, a] for i, a in enumerate(ah)]) for ah in s.acts])
        s._c[si] = (T, Ph, pm, np.einsum('j,rjs->rs', pj, T)); return s._c[si]
    def reach(s):
        L = [{s.init}]
        for t in range(s.T): L.append({k for si in L[-1] for k in np.nonzero(s._trans(si)[0].sum((0, 1)))[0]})
        return L
    def local(s, si, Vn, Cn):
        """Build Local at state si from next-layer V (nS,nH,nG) and cost-to-go Cn (nS,). Returns (Local, Vfun)."""
        T, Ph, pm, Tbar = s._trans(si)
        X = (s.pos[:, 1:, None] == s.goals[None]).astype(float) + s.gh * Vn
        Y = np.einsum('rjs,shg->hgrj', T, X).reshape((s.nH, s.nG, 4) + (3,) * s.nH)
        Yk, q = [], []
        for h in range(s.nH):
            Yh = np.moveaxis(Y[h], 2 + h, 2); Yk.append(Yh.reshape(s.nG, 4, 3, -1))
            oth = [i for i in range(s.nH) if i != h]
            q.append([np.prod([pm[i, a] for i, a in zip(oth, ao)]) for ao in itertools.product(range(3), repeat=len(oth))])
        Yk = np.array(Yk) ** s.kappa; q = np.array(q)
        def V(Pi):
            inner = np.einsum('ka,hgaxy->khgxy', Pi, Yk) ** (s.theta / s.kappa)
            m = np.einsum('khgxy,hy->khgx', inner, q) ** (1 / s.theta)
            return s.eps + np.einsum('khgx,hgx->khg', m, Ph)
        def u(Pi):
            S = np.einsum('khg,hg->kh', V(Pi) ** s.zeta, s.prior)
            return np.mean(S ** (-s.xi), 1) ** s.eta / s.xi
        rng = np.random.default_rng(1); Ps = np.vstack([np.eye(4), rng.dirichlet(np.ones(4), 300)]); us = u(Ps)
        return Local(s.gr * Tbar @ Cn, u, .9 * us.min(), 1.1 * us.max()), V
    def solve(s, solver, beta):
        """Backward induction; solver(local, beta, key)->x.  Returns dict key=(t,state)->(x,local,pi)."""
        L, res = s.reach(), {}
        xT = (s.eps ** (-s.zeta * s.xi)) ** s.eta / s.xi          # terminal: V=eps
        Vn = np.full((s.nS, s.nH, s.nG), s.eps); Cn = np.full(s.nS, xT)
        for t in range(s.T - 1, -1, -1):
            V2, C2 = np.full_like(Vn, s.eps), np.zeros(s.nS)
            for si in L[t]:
                loc, V = s.local(si, Vn, Cn); x = solver(loc, beta, (t, si)); pi = loc.sigma(x, beta)[0]
                V2[si], C2[si] = V(pi[None])[0], pi @ (x + loc.d); res[(t, si)] = (float(x), loc, pi)
            Vn, Cn = V2, C2
        return res
