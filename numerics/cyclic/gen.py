import numpy as np
from system import Game


def rand_game(rng, nonlinear, kind=None):
    S = int(rng.choice([2, 3, 4])); A = int(rng.choice([2, 3])); H = int(rng.choice([1, 2])); G = int(rng.choice([1, 2, 3]))
    Ai, B = 2, int(rng.choice([1, 2])); kind = kind or rng.choice(['dense', 'det', 'bad'])
    shape = (H, G, S, Ai, B, A)
    if kind == 'dense':
        T = rng.dirichlet(np.ones(S) * rng.choice([0.3, 1.0]), size=shape)
    else:   # deterministic transitions, optionally one absorbing bad state 0
        nxt = rng.integers(0, S, size=shape)
        if kind == 'bad': nxt[:, :, 0] = 0; nxt[:, :, 1:] = np.where(rng.random(nxt[:, :, 1:].shape) < 0.25, 0, nxt[:, :, 1:])
        T = np.eye(S)[nxt]
    if rng.random() < 0.4: T = T * rng.uniform(0.7, 1.0, size=shape + (1,))   # termination
    q = rng.dirichlet(np.ones(B), size=(H, S)); p = rng.dirichlet(np.ones(Ai), size=(H, G, S))
    eps = 0.05
    if kind == 'dense': u = rng.random((H, G, S))
    else:  # goal g reached only in state g%S ; others get 0 (plus eps)
        u = np.zeros((H, G, S))
        for k in range(G): u[:, k, (k + 1) % S] = rng.uniform(0.5, 1)
        if kind == 'det': u += 0.2 * rng.random((H, G, S)) * (rng.random((H, G, S)) < 0.3)
    kap, th = (1.0, 1.0) if not nonlinear else (0.0, 0.0)
    if nonlinear:
        while abs(kap - 0) < 0.05: kap = rng.uniform(-2, 1)
        while abs(th - 0) < 0.05: th = rng.uniform(-2, 1)
    return Game(T, q, p, u + eps, *rng.uniform(1, 3, 3), *rng.uniform(0.5, 0.99, 2), float(kap), float(th))
