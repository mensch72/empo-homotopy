"""Multi-start multiplicity search + pseudo-arclength continuation.  usage: python3 search.py {lin|nonlin} N seed budget_s"""
import sys, json, time, numpy as np
from dataclasses import replace
from multiprocessing import Pool
from system import *
from system import _F
from gen import rand_game
from traj import Game3, rand_game3

BETAS = [0, 0.5, 1, 2, 3, 5, 8, 12, 20, 35, 50]
NST = 30


def uniform_start(g, beta):
    S, A = g.dims[:2]; pi = np.full((S, A), 1 / A); c = human(g, pi)[2]
    return np.log(x_given_c(g, c, 0.0, iters=300))


def starts(g, beta, rng, prev):
    S, A = g.dims[:2]; z0 = uniform_start(g, beta); out = list(prev)
    for i in range(NST):
        t = i % 3
        if t == 0: z = z0 + rng.normal(size=S * A) * rng.choice([0.5, 1.5, 3])
        else:
            pi = rng.dirichlet(np.ones(A) * rng.choice([0.3, 1.0]), size=S)
            if t == 2:
                for _ in range(6): pi = 0.5 * pi + 0.5 * phi(g, pi, beta, None)[0]
            z = np.log(x_given_c(g, human(g, pi)[2], beta, iters=60))
        out.append(z)
    return out


def find(g, beta, rng, prev):
    sols = []
    for z in starts(g, beta, rng, prev):
        if not np.all(np.isfinite(z)): continue
        z, nr = newton(g, z, beta)
        if nr < 1e-10 and np.all(np.isfinite(z)):
            if not any(np.abs(z - s).max() < 1e-5 for s in sols): sols.append(z)
    return sols


def trace(g, pend=50.0, mode='beta', p0=0.0, beta0=0.0, maxsteps=600, ps=10.0):
    """pseudo-arclength in (z, p/ps) with p = beta (mode 'beta') or gamma_r at fixed beta0 (mode 'gr'),
    from a Newton solution at p0 upward until p > pend.  Returns (p path, z path, fold p-values)."""
    n = g.dims[0] * g.dims[1]
    gg = lambda p: g if mode == 'beta' else replace(g, gr=p)
    bb = lambda p: p if mode == 'beta' else beta0
    z0s = find(gg(p0), bb(p0), np.random.default_rng(0), [])
    if not z0s: return np.array([p0]), np.zeros((1, n)), []
    z = z0s[0]   # unique at beta=0 / tiny gamma_r (checked by multistart)
    y = np.append(z, p0 / ps); tprev = np.zeros(n + 1); tprev[-1] = 1
    def Jfull(y):
        p = y[-1] * ps; R, J = resid(gg(p), y[:-1], bb(p), True); h = 1e-6
        db = (resid(gg(p + h), y[:-1], bb(p + h)) - R) / h * ps
        return R, np.hstack([J, db[:, None]])
    ds, B, Z, folds = 0.1, [p0], [z.copy()], []
    for _ in range(maxsteps):
        _, Jf = Jfull(y)
        try: t = np.linalg.solve(np.vstack([Jf, tprev]), np.append(np.zeros(n), 1.0))
        except np.linalg.LinAlgError: break
        t /= np.linalg.norm(t)
        ok = False
        while ds > 1e-7 and not ok:
            yp = y + ds * t; yn = yp.copy()
            for it in range(8):
                R, Jf2 = Jfull(yn)
                if not np.all(np.isfinite(R)): break
                if np.abs(R).max() < 1e-11: ok = True; break
                try: dy = np.linalg.solve(np.vstack([Jf2, t]), -np.append(R, t @ (yn - yp)))
                except np.linalg.LinAlgError: break
                yn = yn + dy
            if ok and np.abs(yn - y).max() > 1.5 * ds + 1e-9: ok = False
            if not ok: ds /= 2
        if not ok: break
        if t[-1] * tprev[-1] < 0 and len(B) > 1: folds.append(float(y[-1] * ps))
        tprev = t; y = yn; B.append(y[-1] * ps); Z.append(y[:-1].copy())
        ds = min(ds * 1.5, 1.0) if it <= 3 else ds
        if y[-1] * ps > pend: break
    return np.array(B), np.array(Z), folds


def ve_diag(g, pi):
    """plain fixed-point Ve iteration from V=0 and V=10: (converged both?, max difference)."""
    out = []
    for v0 in (0.0, 10.0):
        V = np.full(g.u.shape, v0)
        for _ in range(4000): V = _F(g, pi, V)
        out.append((V, np.abs(V - _F(g, pi, V)).max()))
    return max(out[0][1], out[1][1]) < 1e-9, float(np.abs(out[0][0] - out[1][0]).max())


def run_instance(args):
    i, seed, mode = args; nonlin = mode == 'nonlin'
    rng = np.random.default_rng(seed * 100003 + i); g = rand_game3(rng) if mode == 'traj' else rand_game(rng, nonlin); Game.ncv = 0; Game3.rho_fail = Game3.nev = 0
    S, A = g.dims[:2]; sols, prev = {}, []
    for b in BETAS:
        sols[b] = find(g, b, rng, prev if b else []); prev = sols[b]
    rho = {b: max((phi_jac_rho(g, z, b) for z in sols[b]), default=np.nan) for b in BETAS}
    B, Z, folds = trace(g)
    # does the traced principal branch reach a found solution at the grid betas?
    match = {}
    for b in BETAS:
        k = np.argmin(np.abs(B - b)); match[b] = bool(len(sols[b]) and np.min([np.abs(Z[k] - z).max() for z in sols[b]]) < 1e-3 and abs(B[k] - b) < 0.5)
    diag = [ve_diag(g, softmax_pi(g, z, 5.0)) for z in sols[5][:2]] if nonlin else []
    r = dict(i=i, size=S * A * g.dims[2] * g.dims[3], dims=g.dims, n={b: len(sols[b]) for b in BETAS}, rho={b: float(rho[b]) for b in BETAS},
             folds=folds, bmax_traced=float(B.max()), ncv=Game.ncv, rho_fail=Game3.rho_fail, nev=Game3.nev, vediag_bad=sum(1 for d in diag if (not d[0]) or d[1] > 1e-7), vediag_n=len(diag))
    if max(r['n'].values()) >= 2:
        r['game'] = g.todict(); r['sols'] = {str(b): [z.tolist() for z in sols[b]] for b in BETAS}
    return r


if __name__ == '__main__':
    mode, N, seed, budget = sys.argv[1], int(sys.argv[2]), int(sys.argv[3]), float(sys.argv[4]); 
    t0 = time.time(); res = []
    with Pool(4) as P:
        for r in P.imap(run_instance, [(i, seed, mode) for i in range(N)]):
            res.append(r)
            if time.time() - t0 > budget: P.terminate(); break
    json.dump(res, open(f'out/results_{mode}.json', 'w'))
    multi = [r for r in res if max(r['n'].values()) >= 2]
    print(mode, 'N', len(res), 'multi', len(multi), 'time', round(time.time() - t0))
