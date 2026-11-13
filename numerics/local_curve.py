"""Zero set of g(beta,x)=x-u(sigma_beta(x)); multiplicity search on synthetic u; LOC-4 check."""
import sys, numpy as np, matplotlib; matplotlib.use('Agg'); import matplotlib.pyplot as plt
from scipy.optimize import brentq
from model import Local, Bus

def roots(loc, beta, n=400):
    xs = np.geomspace(loc.lo, loc.hi, n); gv = loc.g(xs, beta); i = np.nonzero(gv[:-1] * gv[1:] < 0)[0]
    return [brentq(lambda x: loc.g(x, beta)[0], xs[k], xs[k + 1], xtol=1e-13) for k in i]

def synth(v, xi, eta, d):
    v = np.asarray(v); u = lambda Pi: np.mean((Pi @ v.T) ** -xi, 1) ** eta / xi
    lo = (np.mean(v.max(1) ** -xi) ** eta / xi) * .999; hi = (np.mean(v.min(1) ** -xi) ** eta / xi) * 1.001
    return Local(d, u, lo, hi)

def counts(loc, betas, n=300):
    xs = np.geomspace(loc.lo, loc.hi, n); B = len(betas); A = len(loc.d)
    Lg = -np.asarray(betas)[:, None, None] * np.log(xs[None, :, None] + loc.d); Lg -= Lg.max(2, keepdims=True)
    P = np.exp(Lg); P /= P.sum(2, keepdims=True); G = xs[None] - loc.u(P.reshape(-1, A)).reshape(B, n)
    return (G[:, :-1] * G[:, 1:] < 0).sum(1)

BET = [2, 5, 10, 20, 50, 100, 200]
def rand_inst(rng, nA=None, nH=None):
    nA = nA or rng.integers(2, 5); nH = nH or rng.integers(1, 5)
    v = rng.uniform(.05, 1, (nH, nA)); d = rng.uniform(0, 1, nA) * 10 ** rng.uniform(-1, 1.5)
    d[rng.integers(nA)] = 0 if rng.random() < .5 else d[0]; return v, rng.uniform(1, 5), rng.uniform(1, 5), d

def search(N, seed, nA=None, nH=None):
    rng = np.random.default_rng(seed); hits = []
    for k in range(N):
        v, xi, eta, d = rand_inst(rng, nA, nH); loc = synth(v, xi, eta, d); c = counts(loc, BET)
        if c.max() >= 3: hits.append((len(d) * len(v), len(d), len(v), k, BET[int(c.argmax())], int(c.max()), v, xi, eta, d))
    return sorted(hits, key=lambda h: (h[0], h[4], h[5], h[3]))

def loc4(N, seed):
    """Check LOC-4: rigorous (analytic) and tight (sampled) constants; count roots for beta<=.99 beta*."""
    rng = np.random.default_rng(seed); viol = {'rig': 0, 'tight': 0}; tested = 0; bs = []; ratio = np.inf; BG = np.geomspace(.05, 300, 40)
    for k in range(N):
        v, xi, eta, d = rand_inst(rng); loc = synth(v, xi, eta, d); D = d.max() - d.min()
        if D == 0: continue
        vmin, vmax = v.min(1), v.max(1); S = np.mean(vmin ** -xi)
        Lr = .5 * eta * S ** (eta - 1) * np.mean(vmin ** (-xi - 1) * vmax); mr = loc.lo / .999
        Ps = np.vstack([np.eye(len(d)), rng.dirichlet(np.ones(len(d)) * .3, 500)]); w = Ps @ v.T
        Sw = np.mean(w ** -xi, 1)
        gr = -eta * (Sw ** (eta - 1))[:, None] * np.einsum('kh,ha->ka', w ** (-xi - 1), v) / len(v)
        Lt = ((gr.max(1) - gr.min(1)) / 2).max(); mt = (Sw ** eta / xi).min()
        for key, m, L in (('rig', mr, Lr), ('tight', mt, Lt)):
            bstar = 2 * (m + d.min()) * (m + d.max()) / (L * D); bs.append(bstar)
            if key == 'tight':
                tested += 1; c = counts(loc, BG)
                if c.max() >= 2: ratio = min(ratio, BG[np.argmax(c >= 2)] / bstar)   # first multi-root beta / beta*
            b = .99 * bstar
            if b <= 300 and len(roots(loc, b)) != 1: viol[key] += 1; print('LOC-4 VIOLATION', key, v, xi, eta, d, b)
    return viol, tested, float(np.median(bs)), float(ratio)

def plot_curve(ax, loc, bmax, title, nb=200):
    for b in np.linspace(0, bmax, nb): ax.plot([b] * len(r := roots(loc, b)), r, 'k.', ms=2)
    ax.set(xlabel=r'$\beta$', ylabel='x', title=title, yscale='log')

if __name__ == '__main__':
    N = int(sys.argv[1]) if len(sys.argv) > 1 else 20000; hits = search(N, 0); print(f'general search N={N}: {len(hits)} instances with >=3 solutions')
    for h in hits[:3]: print(' |A|=%d |H|=%d try=%d beta=%g nroots=%d xi=%.3f eta=%.3f\n v=%s d=%s' % (*h[1:6], h[7], h[8], np.round(h[6], 3).tolist(), np.round(h[9], 3).tolist()))
    h2 = search(N, 1, 2, 1); print(f'|A|=2,|H|=1 search N={N}: {len(h2)} hits')
    best = (h2 or hits or [None])[0]
    fig, ax = plt.subplots(1, 2, figsize=(9, 3.4))
    if best:
        _, nA, nH, k, b, nr, v, xi, eta, d = best; loc = synth(v, xi, eta, d); plot_curve(ax[0], loc, 25, f'synthetic |A|={nA},|H|={nH}: {nr} roots at beta={b}')
        np.save('out/best.npy', np.array([v, xi, eta, d], dtype=object), allow_pickle=True)
    m = Bus(); res = m.solve(lambda l, b, key: roots(l, b)[0] if len(roots(l, b)) else l.lo, 50.0)
    (x, loc, _) = max(res.values(), key=lambda r: r[1].d.max() - r[1].d.min()); plot_curve(ax[1], loc, 200, 'bus model state (largest D)')
    plt.tight_layout(); plt.savefig('out/local_curves.png', dpi=80)
    print('LOC-4 check:', *loc4(4000, 5), '(violations by constants, #tested, median beta*, min over multi-root instances of beta_first_multi/beta*_tight; must be >=1)')
