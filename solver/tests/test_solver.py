import numpy as np
import pytest
from empo_solver import (Game, Linear, PowerMean, Trajectory, ValidationError, solve, solve_acyclic, solve_horizon,
                         trace, multistart, CyclicError, diagnose)
from empo_solver.core import params_of, residual, newton, z_from_pi
from empo_solver.instances import sys6, random_game


def p1(r):
    return r.pi[1, 2]


# (i) SYS-6 ---------------------------------------------------------------------------------------
def test_sys6_solutions_by_newton():
    g = sys6()
    sols = multistart(g, 40)
    ps = sorted(p1(s) for s in sols)
    assert len(ps) == 3
    assert ps[0] == pytest.approx(0.54587, abs=1e-5) and ps[1] == pytest.approx(0.95412, abs=1e-5)
    third = [s for s in sols if p1(s) > 0.99][0]
    assert 1e-16 < third.one_minus_pi()[1, 2] < 1e-15          # resolved in log-space; 1 - pi not formed in floating point
    for s in sols:
        assert s.residual < 1e-10 and diagnose(s)["Q_negative"]


def test_sys6_method_selection():
    g = sys6()
    tb = trace(g, "beta")                                      # beta 0 -> 2 (path continues to 5 to catch folds)
    assert len(tb.crossings) == 3 and len(tb.folds) == 2
    assert [round(p1(c), 4) for c in tb.crossings[:2]] == [0.5459, 0.9541]
    assert 1e-16 < tb.crossings[2].one_minus_pi()[1, 2] < 1e-15
    assert p1(tb.selected) == pytest.approx(0.54587, abs=1e-5)
    tg = trace(g, "gamma_r")
    assert tg.selected is not None and 1e-16 < tg.selected.one_minus_pi()[1, 2] < 1e-15
    h = solve_horizon(g)
    assert h.success and 1e-16 < h.one_minus_pi()[1, 2] < 1e-15
    s = solve(g)
    assert len(s.solutions) == 3 and s.warnings


# (ii) acyclic agreement -------------------------------------------------------------------------
@pytest.mark.parametrize("variant", ["linear", "trajectory"])
@pytest.mark.parametrize("seed", [0, 1])
def test_acyclic_agreement(variant, seed):
    g = random_game(variant, acyclic=True, seed=seed, beta=1.3)
    a = solve_acyclic(g)
    t = trace(g, "beta").selected
    h = solve_horizon(g)
    assert a.success and t is not None and h.success
    assert np.abs(a.pi - t.pi).max() < 1e-8 and np.abs(a.pi - h.pi).max() < 1e-8
    assert np.abs(a.U / t.U - 1).max() < 1e-8 and np.abs(a.U / h.U - 1).max() < 1e-8
    assert len(solve(g, multistart_n=10).solutions) == 1


def test_cyclic_refused_by_acyclic():
    with pytest.raises(CyclicError):
        solve_acyclic(random_game("linear", acyclic=False))


# (iii) beta = 0 ----------------------------------------------------------------------------------
@pytest.mark.parametrize("variant", ["linear", "powermean", "trajectory"])
def test_beta_zero_uniform(variant):
    g = random_game(variant, seed=3, beta=0.0)
    s = solve(g, multistart_n=10)
    assert len(s.solutions) == 1
    assert np.allclose(s.solutions[0].pi, 1 / g.A, atol=1e-12)
    assert any("SYS-2" in n for n in diagnose(s.solutions[0])["uniqueness"])


# (iv) one cyclic instance per variant -----------------------------------------------------------------
@pytest.mark.parametrize("variant", ["linear", "powermean", "trajectory"])
def test_cyclic_variants_run(variant):
    g = random_game(variant, seed=5, beta=1.5)
    s = solve(g, multistart_n=10)
    assert s.solutions
    for r in s.solutions:
        d = diagnose(r)
        assert r.residual < 1e-9 and d["Q_negative"] and d["U_negative"]
        assert d["Vr_equation_err"] < 1e-9 and d["Ve_fixed_point_err"] < 1e-9 and d["powerlaw_err"] < 1e-9


# (v) validation ---------------------------------------------------------------------------------
def test_validation():
    g = random_game("linear", seed=0)
    with pytest.raises(ValidationError, match="row sums"):
        Game(g.K * 3, g.human)
    with pytest.raises(ValidationError, match="shape"):
        Game(g.K[:, :, :2], g.human)
    with pytest.raises(ValidationError, match="zero successor mass"):
        K = g.K.copy(); K[1, 0] = 0
        Game(K, g.human)
    with pytest.raises(ValidationError, match="beta"):
        Game(g.K, g.human, beta=-1)
    with pytest.raises(ValidationError, match="gamma_r"):
        Game(g.K, g.human, gamma_r=0)
    with pytest.raises(ValidationError, match="gamma_h"):
        Linear(g.human.Kh, g.human.r, gamma_h=1.0)
    with pytest.raises(ValidationError, match="NaN"):
        Linear(g.human.Kh, g.human.r * np.nan)
    with pytest.raises(ValidationError, match="states"):
        Game(random_game("linear", S=4).K, g.human)
    with pytest.raises(ValidationError, match="kappa"):
        PowerMean(random_game("powermean").human.T, *(getattr(random_game("powermean").human, k) for k in "qpu"), kappa=1.5)
