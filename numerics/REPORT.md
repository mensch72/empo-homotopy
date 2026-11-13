# Numerical exploration: non-uniqueness of local steering solutions (NUMERICAL EVIDENCE ONLY, nothing proved)

Run from `numerics/` (python3, numpy/scipy/matplotlib; fixed seeds; ~25 s and ~95 s):
`python3 local_curve.py 20000` (log `out/local_curve.log`), `python3 trace.py 20000` (log `out/trace.log`).
Files: `model.py` (bus model, eqs (1)-(5), `Local` problem), `local_curve.py`, `trace.py`. Plots: `out/local_curves.png`, `out/trace_compare.png`.

## Setup
* Bus model: 4-node cycle, 1 bus (4 moves), 2 humans (3 moves, 3 goals each), horizon T=3 (layered), slip/carry/block noise,
  101 reachable states (default). (3)-(5) with R1/R2 as in STATEMENTS s0. Floor: V_h := eps + (expr), eps=0.2 (terminal V_h=eps). Defaults
  zeta=1, xi=1.5, eta=1.2, kappa=theta=1, gamma_h=gamma_r=0.9. Human goal-marginal policy is used for E_{a_H} in (2) (my choice; s0 does not say).
* Local problem per state: x = u(sigma_beta(x)), x=-U_r(s), d from downstream (-Q = x + d). Roots found by sign changes on a geometric x-grid
  (300-400 pts) + brentq; grid can miss close double roots (so counts are lower bounds).
* Synthetic u(pi) = (1/xi)(mean_h (pi.v_h)^(-xi))^eta, v in [0.05,1], xi,eta in [1,5], d = scale*U[0,1] with scale in [0.1,30], |A|<=4, |H|<=4, beta grid {2,5,10,20,50,100,200}.

## Findings
1. **Multiplicity exists in the local problem (synthetic u).** N=20000 random instances: 623 (3.1%) had >=3 roots at some grid beta; restricted to |A|=2,|H|=1 (another 20000): 865 (4.3%).
   Simplest found (|A|=2,|H|=1, beta=2): v=(0.327,0.96), d=(2.299,0), xi=3.765, eta=3.338 -> roots x=0.663, 1.729, 51.9 (residuals <1e-13),
   pi_1 = 0.048, 0.156, 0.478. Its curve is a backward S: from beta=0, x(0)=u(unif)~1000, fold at beta~13, back to beta~1.8, then a low branch (x~0.85)
   (`out/local_curves.png`, left). A probe over 30000 instances with beta in {.25,.5,1,1.5,2} found 3 roots already at beta=1 (xi=2.01, eta=4.41, v=(0.946,0.100),
   d=(0,18.89): x=1.37, 19.4, 66.4) but none at beta<1; smallest xi*eta among hits ~5.8. Needs large xi*eta (strong convexity of u) and large d-spread. These are searches, not a proof of minimality.
2. **Bus model: no multiplicity found.** Default model: 0/101 states with >1 root at beta=50. Sweep (4 seeds x 7 parameter variants incl. xi=eta=5, gamma_r=0.99,
   kappa=.5/theta=2, zeta=2, eps in {.05,.2,.5} x beta in {5,20,100,500}): 12928 local problems, 0 with >=2 roots. So multiplicity is shown for the abstract
   local problem, but I did NOT exhibit it in the tabular bus model (the terminal x_T = eps^(-zeta*xi*eta)/xi is large and nearly constant, so d has small spread relative to x+d_min; no claim that it cannot happen).
3. **LOC-4 check: no violation.** 3666 random instances (u synthetic), tested with both rigorous analytic constants (m,L from v-range) and tighter sampled constants:
   0 violations (always exactly 1 root at 0.99*beta*). The bound is very conservative: min over multi-root instances of beta_first_multi/beta*_tight = 613 (median beta* ~5e-4). (The test uses synthetic u only, not the bus model.)
4. **Tracer comparison** (K = number of beta steps; Newton `nt` in z=log x with backtracking, no fold recovery; damped fixed point `fp`, alpha=.5; arclength = pseudo-arclength in (beta/bmax, log x)).
   * Bus model (beta_max=50, K=50): warm and arclength agree to 1e-10 on all 101 states; no failures, no beta-turns.
   * Synthetic, 150 multi-root instances, beta_max inside the multi-root window: all methods give the same branch (99%; arclength 100% converged, median 540 u-evals vs ~22 Newton its for K=10).
   * Same instances, beta_max=200 (past folds): the principal path has a beta-turn in 63%. Warm Newton fails/stalls at the fold: converged = same branch = 92% (K=10), 76% (K=40), 54% (K=160); finer steps fail more
     (stays on the folding branch). Damped fp always "converged" (jumps to the final root; 100% match) but with ~10-50x more iterations (288-3863 median). Arclength succeeded 150/150 at median 5250 u-evals (20 steps).
   * Unique-root controls (n=100): warm Newton 99% match; arclength 99% ok (1 failure, not investigated); 3% show a beta-turn even where the beta-grid saw one root.
   Here "same branch" at beta_max with a unique root there is nearly trivial; the informative signal is the failure of Newton at folds (`out/trace_compare.png`: warm K=10 jumps across the S, arclength follows it).

## Caveats
* Evidence only; random search bounds the frequency in my sampling distribution, not existence/non-existence elsewhere. Root counting on a grid can miss root pairs.
* Arclength uses finite-difference derivatives; my Newton lacks a fallback; a robust warm start (bracketing/bisection on g) would not need path tracing for this scalar problem
  (g(beta,.) is scalar: roots of each fixed-beta problem can be bracketed). Path tracing matters for continuing the principal branch (PATH-1).
* Bus-model results depend on my modelling choices (marginal goal policy for a_H in (2), terminal V=eps, noise). Per-state local solves use the downstream solution at the same beta (backward induction), not a joint homotopy.
* Reading R1/R2 as printed in STATEMENTS s0; no check of the PDF.
