"""Simplest multi-solution instance: verification, curve plot, tracer comparison.  usage: python3 plots.py {lin|nonlin}"""
import sys, json, numpy as np
from dataclasses import replace
import matplotlib; matplotlib.use('Agg'); import matplotlib.pyplot as plt
from system import *
from search import find, trace, BETAS

mode = sys.argv[1]
R = json.load(open(f'out/results_{mode}.json')); multi = [r for r in R if 'game' in r]
r = min(multi, key=lambda r: (r['size'], r['i'])); g = Game.fromdict(r['game']); S, A = g.dims[:2]
bm = min(float(b) for b, n in r['n'].items() if n >= 2); sols = [np.array(z) for z in r['sols'][str(bm if bm != int(bm) else int(bm))]]
pis = np.array([softmax_pi(g, z, bm) for z in sols]); sp = pis.max(0) - pis.min(0); s0, a0 = np.unravel_index(sp.argmax(), sp.shape)
coord = lambda z, b: softmax_pi(g, z, b)[s0, a0]
out = [f'instance i={r["i"]} (mode {mode}) dims S,A,H,G={g.dims}, first multiplicity grid beta={bm}, plotted coordinate pi(s{s0})(a{a0})', f'nsol per beta {r["n"]}', f'folds of principal branch {r["folds"]}']
for z in sols:
    v = verify(g, z, bm); out.append(f'sol beta={bm}: x={np.exp(z).round(6).tolist()} pi(s{s0},a{a0})={coord(z,bm):.6g} ' + ' '.join(f'{k}={x:.2g}' for k, x in v.items()))
out.append('pairwise max|z-z\'| = ' + str([round(float(np.abs(sols[i] - sols[j]).max()), 3) for i in range(len(sols)) for j in range(i)]))
json.dump(dict(game=r['game'], beta=bm, sols=[z.tolist() for z in sols]), open(f'out/simplest_{mode}.json', 'w'))
# curve: arclength trace + fine multistart scan
B, Z, folds = trace(g, pend=max(4 * bm, 6) if bm < 20 else 50.0)
fine = np.concatenate([np.arange(0.25, 4.01, 0.125) * bm / 2, [bm * 3, bm * 5]]); rng = np.random.default_rng(0); pts = []
for b in fine:
    for z in find(g, b, rng, []): pts.append((b, coord(z, b)))
pts = np.array(pts)
def warm(gg, ps, bfun, z0):
    z = z0; res = []
    for p in ps:
        z, nr = newton(gg(p), z, bfun(p))
        if nr > 1e-9: res.append(None); break
        res.append(z)
    return res
bt = B.max(); fig, ax = plt.subplots(1, 2, figsize=(9, 3.4))
ax[0].plot(B, [coord(z, b) for z, b in zip(Z, B)], '-', c='C0', label='arclength branch'); ax[0].scatter(pts[:, 0], pts[:, 1], s=8, c='k', label='multistart (30)', zorder=3)
z0 = Z[0]
for K, c in ((10, 'C1'), (80, 'C2')):
    bs_ = np.linspace(0, bt, K + 1)[1:]; w = warm(lambda p: g, bs_, lambda p: p, z0)
    ax[0].plot([b for b, z in zip(bs_, w) if z is not None], [coord(z, b) for b, z in zip(bs_, w) if z is not None], 'x--', c=c, ms=4, label=f'warm Newton K={K}')
    out.append(f'warm beta-steps K={K}: converged {sum(z is not None for z in w)}/{K} steps, last ok beta={max([b for b, z in zip(bs_, w) if z is not None], default=0):.3g}')
ax[0].set_xlabel('beta'); ax[0].set_ylabel(f'pi(s{s0})(a{a0})'); ax[0].legend(fontsize=6); ax[0].set_title('solution curve', fontsize=9)
# gamma_r continuation at fixed beta = bm
gt = g.gr; Bg, Zg, fg = trace(g, pend=gt, mode='gr', p0=0.02, beta0=bm)
ax[1].plot(Bg, [coord(z, bm) for z in Zg], c='C0', label='arclength'); ax[1].set_xlabel('gamma_r'); ax[1].set_title(f'trace in gamma_r at beta={bm}', fontsize=9)
def which(z): return int(np.argmin([np.abs(z - s).max() for s in sols])) if np.abs(z - min(sols, key=lambda s: np.abs(z - s).max())).max() < 1e-4 else -1
z0g = find(replace(g, gr=0.02), bm, np.random.default_rng(0), [])
out.append(f'gamma_r=0.02, beta={bm}: multistart finds {len(z0g)} solution(s)')
zg, nr = newton(g, Zg[np.argmin(np.abs(Bg - gt))], bm); out.append(f'gamma_r arclength (folds {fg}, reached gamma_r={Bg.max():.3f}), Newton polish at target: res {nr:.1e}, sol index {which(zg)} of {len(sols)} (pi={coord(zg,bm):.4g}); all pi: {[round(coord(s,bm),4) for s in sols]}')
for K, c in ((10, 'C1'), (80, 'C2')):
    ps = np.linspace(0.02, gt, K + 1)[1:]; w = warm(lambda p: replace(g, gr=p), ps, lambda p: bm, z0g[0])
    ok = w[-1] is not None; out.append(f'gamma_r warm K={K}: reached target={ok}' + (f', sol index {which(w[-1])} (pi={coord(w[-1],bm):.4g})' if ok else ''))
    ax[1].plot([p for p, z in zip(ps, w) if z is not None], [coord(z, bm) for p, z in zip(ps, w) if z is not None], 'x--', c=c, ms=4, label=f'warm K={K}')
ax[1].legend(fontsize=6); plt.tight_layout(); plt.savefig(f'out/curve_{mode}.png', dpi=110)
open(f'out/trace_{mode}.txt', 'w').write('\n'.join(out)); print('\n'.join(out))
