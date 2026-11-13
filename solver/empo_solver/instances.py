"""Ready-made instances: the SYS-6 two-state game and random games of each variant (for tests and examples)."""
import numpy as np
from .model import Game, Linear, PowerMean, Trajectory


def sys6(beta=2.0):
    """STATEMENTS SYS-6 (Lean `sys6_three_solutions`): S = {0,1}, A = {a0,a1,a2}; state 0: all actions stay (reward 1/20);
    state 1: a0, a1 go to 0 (reward 1/20), a2 stays (reward 1).  gamma_h = 2/3, gamma_r = 4/5, zeta = 2, xi = 1, eta = 3."""
    K = np.zeros((2, 3, 2)); K[0, :, 0] = 1; K[1, :2, 0] = 1; K[1, 2, 1] = 1
    r = np.full((1, 1, 2, 3), 0.05); r[0, 0, 1, 2] = 1.0
    return Game(K, Linear(K[None, None].copy(), r, gamma_h=2 / 3, zeta=2, xi=1, eta=3), beta=beta, gamma_r=0.8, name="SYS-6")


def _kern(rng, shape, support=None, lo=0.5):
    """Random sub-stochastic kernel (last axis successor) with row mass in [lo, 1]; support: boolean mask over the successor axis."""
    P = rng.random(shape)
    if support is not None:
        P = P * support
    P = P / np.maximum(P.sum(-1, keepdims=True), 1e-300)
    return P * rng.uniform(lo, 1, shape[:-1])[..., None]


def random_game(variant="linear", acyclic=False, S=3, A=2, H=2, G=2, seed=0, beta=1.5, gamma_r=0.9, **kw):
    """Random instance.  acyclic: state s only reaches states t < s (state 0 terminal)."""
    rng = np.random.default_rng(seed)
    low = (np.arange(S)[None, :] < np.arange(S)[:, None]) if acyclic else np.ones((S, S), bool)   # low[s,t]
    K = _kern(rng, (S, A, S), low[:, None, :])
    if acyclic:
        K[0] = 0
    if variant == "linear":
        Kh = _kern(rng, (H, G, S, A, S), low[None, None, :, None, :])
        if acyclic:
            Kh[:, :, 0] = 0
        hv = Linear(Kh, rng.uniform(0.1, 1, (H, G, S, A)), gamma_h=kw.get("gamma_h", 0.8),
                    zeta=kw.get("zeta", 1.5), xi=kw.get("xi", 1.0), eta=kw.get("eta", 1.0))
    elif variant == "powermean":
        B = 2
        T = _kern(rng, (H, G, S, A, B, A, S), low[None, None, :, None, None, None, :])
        if acyclic:
            T[:, :, 0] = 0
        hv = PowerMean(T, rng.dirichlet(np.ones(B), (H, S)), rng.dirichlet(np.ones(A), (H, G, S)),
                       rng.uniform(0.1, 1, (H, G, S)), kappa=kw.get("kappa", 0.5), theta=kw.get("theta", 0.5),
                       gamma_h=kw.get("gamma_h", 0.8), zeta=1.5, xi=1.0, eta=1.0)
    elif variant == "trajectory":
        P = _kern(rng, (H, S, A, A, S), low[None, :, None, None, :], lo=0.5)
        if acyclic:
            P[:, 0] = 0
        hv = Trajectory(P, gamma_h=kw.get("gamma_h", 0.3), zeta=kw.get("zeta", 1.0), xi=1.0, eta=1.0)
    else:
        raise ValueError(variant)
    return Game(K, hv, beta=beta, gamma_r=gamma_r, name=f"random-{variant}-{seed}")
