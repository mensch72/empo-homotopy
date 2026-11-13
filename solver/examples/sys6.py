"""Reproduce the SYS-6 table (which solution each method selects) and plot the beta-solution curve.
Run:  python3 solver/examples/sys6.py      (numerical evidence; the three solutions are proved to exist in Lean, sys6_three_solutions)"""
import os, sys
sys.path.insert(0, os.path.join(os.path.dirname(__file__), ".."))
import numpy as np
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
from empo_solver import trace, solve_horizon, multistart
from empo_solver.core import logit_pi
from empo_solver.instances import sys6

g = sys6(beta=2.0)


def desc(r):
    return f"pi(1)(stay) = {r.pi[1, 2]:.5f}, 1 - pi(1)(stay) = {r.one_minus_pi()[1, 2]:.3e}"


tb, tg, h, ms = trace(g, "beta", hmax=0.25), trace(g, "gamma_r"), solve_horizon(g), multistart(g, 40)
print("method                          selected solution")
print("beta-trace 0 -> 2 (1st crossing)", desc(tb.selected))
for i, c in enumerate(tb.crossings[1:], 2):
    print(f"   crossing #{i} on the same path  ", desc(c))
print("beta-trace folds at beta ~", [round(f["lam"], 3) for f in tb.folds], "| status:", tb.status)
print("gamma_r-trace from 1e-3 to 0.8  ", desc(tg.selected), "| crossings:", len(tg.crossings))
print(f"solve_horizon (T = {h.iterations})          ", desc(h))
print("multistart finds                ", sorted(round(float(s.pi[1, 2]), 5) for s in ms))

lam = tb.lam
y = np.array([logit_pi(g, z, b, 1, 2) for z, b in zip(tb.z, lam)])
fig, ax = plt.subplots(figsize=(6, 4))
ax.plot(lam, y, "-", color="#1f77b4", lw=1.8, label="solution branch from $\\beta=0$")
ax.axvline(2.0, color="0.6", ls="--", lw=1)
ax.plot([2.0] * len(tb.crossings), [logit_pi(g, c.z, 2.0, 1, 2) for c in tb.crossings], "o", color="#d62728", label="solutions at $\\beta=2$")
for f in tb.folds:
    ax.axvline(f["lam"], color="0.85", lw=0.8, zorder=0)
ax.set_xlabel("$\\beta$"); ax.set_ylabel("logit $\\pi(1)(\\mathrm{stay})$")
ax.set_title("SYS-6: arclength-traced solution curve (folds at grey lines)")
ax.legend(frameon=False, loc="upper left"); fig.tight_layout()
out = os.path.join(os.path.dirname(__file__), "sys6_curve.png")
fig.savefig(out, dpi=130)
print("saved", out)
