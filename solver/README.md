# empo_solver: solving the steering equations (STATEMENTS §0) with honest diagnostics

Tabular solver for the target system of `notes/STATEMENTS.md` §0: robot side (4), (5), (9) with terminal states,
human value variants linear (6), power-mean (6'), discounted trajectory (7T).  Python 3, numpy, scipy.
Everything here is **numerical evidence (N), not proof**; the cited statements say what is proved.
Run tests: `python3 -m pytest solver/tests` (about 5 s).  Example: `python3 solver/examples/sys6.py`.

## Usage
```python
import sys; sys.path.insert(0, "solver")
from empo_solver import solve, diagnose, trace, Game, Linear
from empo_solver.instances import sys6, random_game

g = sys6(beta=2.0)                       # or Game(K, Linear(Kh, r, gamma_h=.., zeta=.., xi=.., eta=..), beta=.., gamma_r=..)
sols = solve(g, multistart_n=40)         # acyclic -> exact; else beta-trace + horizon (+ multistart)
print(sols.summary())                    # all distinct solutions, which method found which, warnings
r = sols.solutions[0]                    # Result: pi, Q, Vr, U, residual, iterations, success, method, notes
print(r.pi, r.one_minus_pi())            # 1 - pi by a stable formula (no cancellation)
print(diagnose(r))                       # conditions, conditioning, fixed-point radius, applicable theorems
tr = trace(g, "beta")                    # path in beta from 0; tr.crossings = all solutions at the target, in order
print(tr.selected.pi, tr.folds)          # first crossing; approximate fold locations
```
Data: `K[s,a,s']` (rows sum <= 1; an all-zero state is terminal: pi uniform, excluded from the unknowns).
`Linear(Kh[h,g,s,a,s'], r[h,g,s,a])`, `PowerMean(T[h,g,s,i,b,a,s'], q, p, u, kappa, theta)` (as `numerics/cyclic/system.py`),
`Trajectory(Pbar[h,s,a_h,a,s'])`; all take `gamma_h, zeta, xi, eta`.  Invalid data raises `ValidationError`.

## Method: guarantees and non-guarantees
Unknowns are z = log(-Q) of non-terminal states (Q spans many orders of magnitude, e.g. 1e5..1e16), pi = softmax(-beta z),
residual log(gamma_r K (c + w)) - z; Jacobians by complex step (exact).  Output is checked by the residual only up to ~1e-10.

| method | what it does | guarantee | not guaranteed |
|---|---|---|---|
| `solve_acyclic` | backward induction by topological rank | exact; the solution is unique [SYS-3, L] | refuses cyclic games (`CyclicError`) |
| `solve_horizon` | T-step unrolled (acyclic, uniquely solvable) game, T = 1, 2, ... | each layer exact; reports non-convergence, period of a limit cycle | convergence; selects one solution, not necessarily a "natural" one |
| `trace` (beta, gamma_r, gamma_h) | pseudo-arclength continuation, fold detection, all crossings of the target | start at beta = 0 is unique [SYS-2, L]; follows the branch through folds | finds only the branch component of the start; gamma_r/gamma_h starts are not proved unique; may stop at a singular point (reported) |
| `multistart` | random policies, Newton, scipy `root` fallback | every returned point has small residual | completeness: absent solutions may exist |
| `solve` | front end, merges and labels | warns when > 1 distinct solution | nothing says the list is complete (existence is open [SYS-4]) |

`diagnose` reports: all solution conditions (Q < 0, power law, Vr and Ve equations, terminal convention), min(1 - pi),
log10 range of -Q, spectral radius of the Jacobian of the naive map pi -> powerlaw(Q(U(pi))) (< 1: plain iteration
converges locally), smallest singular values of Jz and of the continuation Jacobian [Jz | J_beta] (small: fold), and
which proved uniqueness results apply: acyclic [SYS-3], beta = 0 [SYS-2], beta <= 1 only partial [SYS-1, SYS-5],
otherwise "not guaranteed; non-unique examples exist [SYS-6]".

## Which solution does each method select on SYS-6 (beta = 2, gamma_r = 4/5)?
Three solutions exist [SYS-6, L]: pi(1)(stay) = 0.54587, 0.95412, and 1 - 4.9e-16.

| method | selected |
|---|---|
| beta-trace 0 -> 2, first crossing | 0.54587 (path folds at beta = 2.586, 1.139, then crosses 0.95412 and 1 - 4.9e-16) |
| gamma_r-trace from 1e-3 to 0.8 | 1 - 4.9e-16 (the only crossing) |
| `solve_horizon` (T = 147) | 1 - 4.9e-16 |
| `multistart` (40 starts) | all three |

Curve: `solver/examples/sys6_curve.png`.  So "the" solution of a cyclic game with beta > 1 depends on the method.

## Limitations
* Small tabular games only (Jacobian by n complex-step evaluations, n = |non-terminal states| x |A|).
* Power-mean variant: `Ve` is found by plain iteration (may not converge; then U = NaN and the point is rejected);
  UniqEval for kappa, theta < 1 is open [SYS-P].  An acyclic power-mean game with U < 0 cannot exist (the lowest state has Ve = 0).
* Trajectory variant needs spectral radius of gamma_h M_pi < 1 along the iteration (else NaN, rejected) [SYS-TE].
* Continuation can stop at branch points or jump branches at very large steps (tangent-angle test mitigates).
* No proof of existence [SYS-4]; random tests found 1 solution in 72 random cyclic instances, SYS-6 is hand-built.
