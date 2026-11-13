"""Warm-start continuation vs pseudo-arclength predictor-corrector for g(beta,x)=0 (work in z=log x, t=beta/bmax)."""
import sys, warnings, numpy as np, matplotlib; warnings.filterwarnings('ignore'); matplotlib.use('Agg'); import matplotlib.pyplot as plt
from local_curve import synth, roots, rand_inst, counts, BET, plot_curve
from model import Bus

def G(loc, beta, z): return z - np.log(loc.phi(np.exp(z), beta)[0])
def newton(loc, beta, x0, tol=1e-10, maxit=60):
    z, h = np.log(x0), 1e-6
    for it in range(maxit):
        g = G(loc, beta, z)
        if abs(g) < tol: return np.exp(z), it, True
        dg = (G(loc, beta, z + h) - G(loc, beta, z - h)) / (2 * h)
        dz = -g / dg if abs(dg) > 1e-12 else -np.sign(g)
        for _ in range(25):
            if abs(G(loc, beta, z + dz)) < abs(g) or abs(dz) < 1e-12: break
            dz /= 2
        z += dz
    return np.exp(z), maxit, abs(G(loc, beta, z)) < tol
def fixedpoint(loc, beta, x0, alpha=.5, tol=1e-10, maxit=2000):
    x = x0
    for it in range(maxit):
        y = loc.phi(x, beta)[0]
        if abs(y - x) < tol * x: return x, it, True
        x += alpha * (y - x)
    return x, maxit, False

def warm(loc, bmax, K, inner=newton):
    x = loc.phi(1., 0.)[0]; its = 0; ok = True        # beta=0: sigma uniform, x=u(unif)
    for b in np.linspace(0, bmax, K + 1)[1:]:
        x, i, o = inner(loc, b, x); its += i; ok &= o
    return x, its, ok

def arclength(loc, bmax, h0=.05, hmax=.25, maxstep=4000, path=None):
    """Pseudo-arclength on G(t,z)=0 from t=0 (beta=0). Returns x at beta=bmax, #steps, #corrector its, ok, #beta-turns."""
    d = 1e-6; Gt = lambda t, z: (G(loc, bmax * (t + d), z) - G(loc, bmax * (t - d), z)) / (2 * d)
    Gz = lambda t, z: (G(loc, bmax * t, z + d) - G(loc, bmax * t, z - d)) / (2 * d)
    def tang(y, prev):
        a, c = Gt(*y), Gz(*y); tau = np.array([-c, a]) / np.hypot(a, c); return tau if tau @ prev > 0 else -tau
    y = np.array([0., np.log(loc.phi(1., 0.)[0])]); tau = tang(y, np.array([1., 0.])); h = h0; steps = cits = turns = 0
    if path is not None: path.append((0., np.exp(y[1])))
    while steps < maxstep:
        yp = y + h * tau; yn = yp.copy(); ok = False
        for it in range(12):
            F = np.array([G(loc, bmax * yn[0], yn[1]), tau @ (yn - yp)]); cits += 1
            if abs(F[0]) < 1e-10: ok = True; break
            J = np.array([[Gt(*yn), Gz(*yn)], tau]); yn = yn + np.linalg.solve(J, -F)
        if not ok or np.linalg.norm(yn - y) > 2 * h: h /= 2; cits += 0; 
        else:
            steps += 1; tn = tang(yn, tau); turns += (tn[0] * tau[0] < 0)
            if yn[0] >= 1:                                   # crossed beta=bmax: solve there from interpolation
                s = (1 - y[0]) / (yn[0] - y[0]); z0 = y[1] + s * (yn[1] - y[1]); x, i, o = newton(loc, bmax, np.exp(z0))
                if path is not None: path.append((bmax, x))
                return x, steps, cits + i, o, int(turns)
            y, tau = yn, tn; h = min(h * (1.5 if it < 4 else 1), hmax)
            if path is not None: path.append((bmax * y[0], np.exp(y[1])))
            if y[0] < -1e-3: return np.nan, steps, cits, False, int(turns)   # returned to beta<0
        if h < 1e-9: break
    return np.nan, steps, cits, False, int(turns)

def compare(loc, bmax, Ks=(10, 40, 160)):
    r = roots(loc, bmax); xa, st, ci, oka, tn = arclength(loc, bmax); out = dict(nroots=len(r), arc=xa, arc_ok=oka, turns=tn, arc_cost=(st, ci, loc.n))
    out['arc_idx'] = int(np.argmin(abs(np.array(r) - xa))) if oka and r else -1
    for K in Ks:
        for nm, fn in (('nt', newton), ('fp', fixedpoint)):
            loc.n = 0; x, its, ok = warm(loc, bmax, K, fn); out[f'{nm}{K}'] = (x, its, ok, bool(ok and oka and abs(x - xa) < 1e-6 * xa), loc.n)
    return out

def synthetic_study(N=20000, nmax=150):
    rng = np.random.default_rng(7); rows = []; nmult = nctl = 0
    for k in range(N):
        if nmult >= nmax and nctl >= 100: break
        v, xi, eta, d = rand_inst(rng); loc = synth(v, xi, eta, d); c = counts(loc, BET)
        if c.max() >= 3 and nmult < nmax: nmult += 1; rows.append((True, compare(loc, BET[int(c.argmax())]), loc)); rows.append(('end', compare(loc, 200.), loc))
        elif c.max() == 1 and nctl < 100 and k % 7 == 0: nctl += 1; rows.append((False, compare(loc, BET[-1]), loc))
    print('SYNTHETIC (beta_max = a beta with >=3 roots for multi instances; 200 for unique-root controls)')
    for flag, nm in ((True, 'multi-root, beta_max inside multi-root window'), ('end', 'multi-root instances, beta_max=200 (past folds)'), (False, 'unique-root controls, beta_max=200')):
        R = [r for f, r, _ in rows if f == flag]; print(f' {nm}: n={len(R)}  arclength ok={np.mean([r["arc_ok"] for r in R]):.2f}  arc steps/corr its/u-evals median={np.median([r["arc_cost"][0] for r in R]):.0f}/{np.median([r["arc_cost"][1] for r in R]):.0f}/{np.median([r["arc_cost"][2] for r in R]):.0f}  frac with beta-turn={np.mean([r["turns"] > 0 for r in R]):.2f}')
        for K in (10, 40, 160):
            for m in ('nt', 'fp'):
                a = [r[f'{m}{K}'] for r in R]; print(f'   warm {m} K={K}: converged {np.mean([x[2] for x in a]):.2f}  same-branch-as-arclength {np.mean([x[3] for x in a]):.2f}  median its {np.median([x[1] for x in a]):.0f}')
    return rows

def bus_study(bmax=50., K=50):
    m = Bus(); cnt = {}
    def mk(method):
        wst = {}
        def f(loc, beta, key):
            if method == 'arc': x, st, ci, ok, tn = arclength(loc, beta); cnt[key] = cnt.get(key, 0) + 1; f.fail += not ok; f.turns += tn; return x if ok else loc.lo
            # warm: continue across whole beta schedule, per-state memory of previous x
            x0 = wst.get(key, loc.phi(1., 0.)[0]); x, i, o = newton(loc, beta, x0); f.its += i; f.fail += not o; wst[key] = x; return x
        f.fail = f.its = f.turns = 0; return f, wst
    fa, _ = mk('arc'); fw, _ = mk('warm'); out = {}
    for b in np.linspace(0, bmax, K + 1)[1:]: resw = m.solve(fw, b)
    resa = m.solve(fa, bmax)
    dx = [abs(resw[k][0] - resa[k][0]) / resa[k][0] for k in resa]; nr = [len(roots(resa[k][1], bmax)) for k in resa]
    print(f'BUS model default (nS reachable solves={len(resa)}), beta_max={bmax}: arclength failures={fa.fail}, beta-turns={fa.turns}, warm failures={fw.fail}')
    print(f' max rel diff warm-vs-arclength x = {max(dx):.2e}; states with >1 root at beta_max: {sum(n > 1 for n in nr)}/{len(nr)}; max #roots {max(nr)}')
    return m, resa

def bus_sweep():
    print('BUS sweep: states with >=2 / >=3 roots at beta in {5,20,100,500} over configs (warm-chain downstream)')
    tot = [0, 0, 0]; ex = None
    for seed in range(4):
        for kw in (dict(), dict(eps=.05), dict(gr=.99), dict(xi=3., eta=3.), dict(xi=4., eta=4., gr=.99, eps=.05), dict(kappa=.5, theta=2.), dict(zeta=2., xi=3., eta=3., gr=.99), dict(xi=5., eta=5., gr=.99, eps=.5)):
            m = Bus(seed=seed, **kw)
            for b in (5., 20., 100., 500.):
                x = {}
                def f(loc, beta, key, x=x):
                    r = roots(loc, beta); x[key] = len(r); return r[0] if r else loc.lo   # lowest root (just to continue)
                m.solve(f, b); c = np.array(list(x.values())); tot[0] += len(c); tot[1] += (c >= 2).sum(); tot[2] += (c >= 3).sum()
                if (c >= 3).any() and ex is None: ex = (seed, kw, b)
    print(f' local problems={tot[0]}, with >=2 roots={tot[1]}, with >=3 roots={tot[2]}; first >=3 example (seed,kw,beta)={ex}'); return ex

if __name__ == '__main__':
    rows = synthetic_study(int(sys.argv[1]) if len(sys.argv) > 1 else 20000)
    fig, ax = plt.subplots(1, 2, figsize=(9, 3.4))
    f, r, loc = next((a for a in rows if a[0] == 'end' and a[1]['turns'] > 0), rows[0]); bm = 200.
    plot_curve(ax[0], loc, 200, f'S-curve, warm start K=10 vs arclength (beta_max={bm})')
    path = []; arclength(loc, bm, path=path); P = np.array(path); ax[0].plot(P[:, 0], P[:, 1], 'r-', lw=.8, label='arclength')
    xs = []; x = loc.phi(1., 0.)[0]
    for b in np.linspace(0, bm, 11)[1:]: x, _, _ = newton(loc, b, x); xs.append(x)
    ax[0].plot(np.linspace(0, bm, 11)[1:], xs, 'b.-', ms=5, label='warm Newton K=10'); ax[0].legend(fontsize=7); ax[0].set_xlim(0, 200 if bm > 100 else 2.5 * bm)
    ax[1].hist([min(r['arc_cost'][2], 3000) for fl, r, _ in rows if fl is True], bins=30); ax[1].set(title='arclength u-evals (multi-root instances)', xlabel='u evaluations')
    plt.tight_layout(); plt.savefig('out/trace_compare.png', dpi=80)
    bus_study(); bus_sweep()
