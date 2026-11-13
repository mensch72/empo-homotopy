# Cyclic games, SYS-5: numerical search for several solutions (EVIDENCE ONLY, nothing proved)

Run from `numerics/cyclic/` (python3, numpy/scipy/matplotlib, fixed seeds, 4 cores):
`python3 search.py lin 100000 1 280` / `nonlin ... 2 240` / `traj ... 3 150` (mode, max N, seed, wall budget s; writes `out/results_*.json`),
`python3 plots.py {lin|nonlin|traj}` (verification, `out/simplest_*.json`, `out/trace_*.txt`, `out/curve_*.png`), `python3 summarize.py`.
Files: `system.py` (system of STATEMENTS s0 + power-mean Ve, analytic Jacobians), `gen.py` (instances), `traj.py` (variant 3), `search.py`.
NB: `results_lin.json` was produced before the safeguarded Ve-solver edit (irrelevant for kappa=theta=1) and the generic `trace()` refactor.

## Setup
* Unknown z = log x, x = -Q (S*A); pi = softmax(-beta z); residual R = 1 - gamma_r (K(c + w_beta(x)))/x, c = -U(pi). Solutions of R=0 <-> solutions of s0.
  Newton with analytic Jacobian (Ve by implicit differentiation, checked vs finite differences ~1e-9), residual < 1e-10 (relative, per entry).
* Per instance and beta in {0,.5,1,2,3,5,8,12,20,35,50}: 30 starts (1/3 log-normal around the beta=0 solution, 1/3 Dirichlet pi -> x(U) -> Newton, 1/3 six damped
  pi-map steps -> Newton) + all solutions of the previous beta. Dedup: max|dz| < 1e-5. Pseudo-arclength from beta=0 (unique) to 50; fold = sign change of dbeta/ds.
* Instances: |S| 2-4, |A| 2-3, |H| 1-2, |G| 1-3 (|A_h|=2, |B|=1-2); kinds dense Dirichlet / deterministic / deterministic with absorbing bad state; goal rewards only in one
  state per goal, eps=0.05 floor; 40% with termination (row sums 0.7-1). zeta, xi, eta in [1,3], gamma in [.5,.99].
* Nonlinear Ve (owner's power mean): kappa, theta in [-2,1] minus (-.05,.05). Robot kernel K = average of T over h,g (uniform), a_h (p), b (q) (my reading).
  Ve by 8 fixed-point steps from 0, safeguarded Newton, else plain iteration (20000 its). Variant 3 (traj): X = 1 + sum max_ah Pbar^zeta X, no p, K = average over h, a_h uniform, b (q); T row sums in [.3,1].

## Results (N = instances searched in the compute budget; "multi" = >=2 distinct verified solutions at some grid beta)
| mode | N | multi | smallest grid beta with multi | multi at grid beta<=1 | max #solutions | principal branch has fold |
|---|---|---|---|---|---|---|
| linear (kappa=theta=1) | 229 | 23 (10%) | 2 (fold interval (1.09, ...) in best case) | 0 | 5 | 6 (min fold beta 1.09) |
| power-mean (kappa,theta<1) | 74 | 9 (12%) | 8 | 0 | 3 | 3 (min fold 2.33) |
| trajectory (variant 3) | 168 | 53 (32%) | 1 (instance 61: window ~(0.92,1.23)) | 1 | 9 | 12 (min fold 1.00) |
* No instance had multiplicity at beta=0 or 0.5. Linear: none at beta<=1 in 229 tries (best fold beta = 1.09, instance 184; 1.14 for instance 168). Not found != does not exist: N is small and the
  grid is coarse (beta=0.5, 1 only; fine scans only for the simplest instance). Trajectory variant: multiplicity at beta<1 (0.95-1.2 on a 0.05 grid, 3 solutions, 30 starts) in `out/trace_traj.txt`.
* Ve fixed-point diagnostics (nonlinear): 0 non-convergences of the Ve iteration in 74 instances (the 920 earlier were a NaN bug, fixed); at 74 solutions the plain
  iteration from V=0 and V=10 converged to the same Ve (< 1e-7). Uniqueness of Ve given pi is NOT established (only sampled); 9 of 750 random-pi tests in a pre-fix probe were NaN artefacts.
* Variant 3: spectral radius of M >= 1 (X infinite) in 52374 of 3.78e6 evaluations of the map (1.4%), mostly in Newton trial points / extreme pi, never at a reported solution.
  With zeta >= 1 and entries <= 1, M <= Pbar entrywise so rho(M) < 1 whenever Pbar has row sums < 1; failures need row sums ~1 and concentrated pi.
* Jacobian of pi -> normalise(x(U(pi))^-beta) at solutions: spectral radius (max over instances) exceeds 1 already at beta=3 (linear: 0.28, 0.47, 0.85, 1.7, 3.8, 9.3, ... 42.8 at beta=.5,1,2,3,5,8,...,50;
  nonlinear up to 85; traj up to 187): not contraction-like for beta >~ 2, below 1 at beta<=1 in linear/nonlinear (traj: 1.55 at beta=1). Uniqueness for small beta is therefore not a contraction property of this map in general.

## Simplest multi-solution instance (linear, `out/simplest_lin.json`, instance 168; verified by `verify()` with separate loops and plain iteration)
S=2, A=3, H=G=1, B=1, A_h=2, deterministic: state 0 absorbing under all a; state 1: a0,a1 -> 0, a2 -> 1 (self-loop). p(1)=((.58148,.41852),(.65845,.34155)) over a_h at s=0,1;
u = (0.05, 1.02066) (eps incl.); zeta=1.58597, xi=1.52669, eta=2.55845, gamma_h=0.651255, gamma_r=0.823649. At beta=2 three solutions, x(s0,.)=784971.65645 (uniform pi) and x(s1,.)=
(784971.65645, 784971.65645, v): v = 547265.708 (pi(s1,a2)=0.50707), 99279.910 (0.96900), 0.00603 (pi=1-1e-8-ish); residuals <= 7e-15 (relative), Q<0, Ve>=0.14, X>=0.046, pairwise max|dz| >= 1.7.
Multiplicity for beta in about (1.14, 2.90) (folds 1.1434, 2.8953; beta=1.25..2.75 on a 0.25 grid). Caveat: conditioning is extreme (c ~ 8e5 since X is small); the 3rd solution is almost deterministic.
Nonlinear simplest (instance 47, S=2,A=2,H=1,G=2, beta=35, three solutions, x of order 2..14, `out/trace_nonlin.txt`, `out/simplest_nonlin.json`): well conditioned.

## Tracers (`out/curve_*.png`, `out/trace_*.txt`)
* beta from 0 (linear, instance 168): warm Newton K=10 stalls at beta=2.48, K=80 at 2.89 (the fold); arclength passes both folds (path forward-back-forward) and reaches beta=50.
  Nonlinear instance 47: no fold on the principal branch; warm and arclength agree and reach beta=50 -- the other two solutions are on a separate (isolated) component, found only by multistart.
  Traj instance 61: arclength/warm both stop at beta~1.234 (fold; ds collapsed, not resolved).
* gamma_r from 0.02 at fixed beta (multistart: 1 solution at 0.02 in linear and traj, 3 in nonlinear): arclength and warm (K=10, 80) all end at the SAME solution; linear: the near-deterministic one
  (pi(s1,a2)=1), NOT the near-uniform branch reached from beta=0; nonlinear: pi=0.788 (index 0); traj: the third (pi=0.008).
## Caveats
Small N (random search, one distribution); grid beta coarse; wall budgets were not equal (linear 292 s, nonlinear 454 s (slow Ve), traj 153 s); instances with tiny/huge x are numerically harsh; "simplest" = smallest S*A*H*G.
Ambiguities in s0: with the original linear Ve the fixed-point of Ve needs gamma_h < 1 or absorbing terminals (F4); K for the robot is not defined by s0 (here: average of T); the human policy p was fixed random.
