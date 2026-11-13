"""Honest diagnostics of a computed solution: all solution conditions, conditioning, stability of the naive iteration,
and which proved uniqueness results apply.  Numerical output is evidence, not proof."""
import numpy as np
from .core import params_of, residual, jacobian, robot_given_pi, ranks, lse, softmax_full


def uniqueness_notes(game):
    """Which proved results apply to this instance (statement ids of notes/STATEMENTS.md s0)."""
    out = []
    if ranks(game) is not None:
        out.append("acyclic: the solution is unique [SYS-3, Lean], for all beta, gamma_r")
    if game.beta == 0:
        pm = type(game.human).__name__ == "PowerMean" and (game.human.kappa < 1 or game.human.theta < 1)
        out.append("beta = 0: unique if UniqEval holds [SYS-2, Lean]; for the power-mean variant with kappa or theta < 1 "
                   "UniqEval is open [SYS-P]" if pm else "beta = 0: unique [SYS-2, Lean; UniqEval holds for this variant, SYS-L/SYS-T]")
    elif game.beta <= 1:
        out.append("beta <= 1: solutions with the same U coincide [SYS-1, Lean]; full uniqueness is open [SYS-5]")
    if not out:
        out.append("not guaranteed; non-unique examples exist [SYS-6]")
    elif ranks(game) is None and game.beta != 0:
        out.append("cyclic: beta > 1 gives no uniqueness guarantee; non-unique examples exist [SYS-6]" if game.beta > 1 else
                   "cyclic: no further guarantee")
    return out


def fixed_point_jacobian_radius(game, pi):
    """Spectral radius of the Jacobian of the naive map pi -> powerlaw(Q(U(pi))) at pi (logit coordinates, last action
    pinned; spectral radius is coordinate independent).  < 1: plain fixed-point iteration converges locally."""
    nt, A, beta = game.nt, game.A, game.beta
    if A == 1 or len(nt) == 0:
        return 0.0
    l0 = np.log(pi[nt][:, :-1]) - np.log(pi[nt][:, -1:])
    m = l0.size

    def G(l):
        lf = np.concatenate([l.reshape(len(nt), A - 1), np.zeros((len(nt), 1), dtype=l.dtype)], axis=1)
        full = np.full((game.S, A), 1.0 / A, dtype=l.dtype)
        full[nt] = np.exp(lf - lse(lf)[:, None])
        U, _ = game.human.evaluate(full)
        Q, _ = robot_given_pi(game, full, U)
        z = np.log(-Q[nt])
        out = -beta * (z[:, :-1] - z[:, -1:])
        return out.ravel()

    J = np.empty((m, m))
    h = 1e-30
    lc = l0.ravel().astype(complex)
    for j in range(m):
        lc[j] += 1j * h
        J[:, j] = G(lc).imag / h
        lc[j] -= 1j * h
    return float(np.abs(np.linalg.eigvals(J)).max())


def diagnose(res):
    """Dictionary of diagnostics for a Result."""
    g, p = res.game, res.params
    d = {"residual_log": res.residual, "method": res.method}
    ok = np.all(np.isfinite(res.Q)) and np.all(res.U < 0)
    d["U_negative"] = bool(np.all(res.U < 0))
    if ok:
        nt = g.nt
        d["Q_negative"] = bool(np.all(res.Q[nt] < 0))
        d["pi_rowsum_err"] = float(np.abs(res.pi.sum(1) - 1).max())
        l = -p.beta * np.log(-res.Q[nt])
        d["powerlaw_err"] = float(np.abs(np.log(res.pi[nt]) - (l - lse(l)[:, None])).max())
        d["Q_equation_err"] = float(np.abs(res.Q - p.gamma_r * g.K @ res.Vr).max() / max(1e-300, np.abs(res.Q).max()))
        d["Vr_equation_err"] = float(np.abs(res.Vr - res.U - (res.pi * res.Q).sum(1)).max() / np.abs(res.Vr).max())
        d["terminal_ok"] = bool(np.all(res.Q[g.terminal] == 0) and np.allclose(res.pi[g.terminal], 1 / g.A))
        Ve = res.game.human.evaluate(res.pi, p.gh)[1].get("Ve")
        if Ve is not None:
            F = g.human.phi(res.pi, Ve, p.gh)
            d["Ve_fixed_point_err"] = float(np.abs(F - Ve).max() / np.abs(Ve).max())
        d["min_one_minus_pi"] = float(res.one_minus_pi()[g.nt].min())
        d["log10_range_of_-Q"] = float(np.ptp(np.log10(-res.Q[nt])))
        d["fixed_point_map_spectral_radius"] = fixed_point_jacobian_radius(g, res.pi)
        Jz, Jb = jacobian(g, res.z, p, "beta")
        d["sigma_min_Jz"] = float(np.linalg.svd(Jz, compute_uv=False)[-1])
        d["sigma_min_continuation_jacobian"] = float(np.linalg.svd(np.column_stack([Jz, Jb]), compute_uv=False)[-1])
        d["nondegenerate"] = d["sigma_min_Jz"] > 1e-8
    d["uniqueness"] = uniqueness_notes(g)
    return d
