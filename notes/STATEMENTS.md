# Statements (source of truth for targets; release 0.1 scope)

Status marks: **L** = proved in Lean (name given), **I** = informal proof only, **N** = numerical
evidence only, **?** = open.  Nothing marked I/N/? may be reported as verified.

## 0. Target system (owner decisions 2026-11-13)

Robot side as in arXiv:2508.00159v2 Table 2, eqs. (4), (5), (7)–(9) (read from the LaTeX source);
human value equation (6) replaced by eq. (5) of the proposal PDF (power means, κ, θ ≤ 1).
Phase 1 (human policies π_h) is exogenous.

    (4)  Q_r(s,a)   = γ_r E_g E_{a_H∼π_H(s,g)} E_{s'} V_r(s')
    (5)  π_r(s)(a)  ∝ (−Q_r(s,a))^(−β)
    (6') V_h(s,g)   = E_{a_h∼π_h(s,g)} ( E_{a_-h} ( E_{a_r∼π_r(s)} (E_{s'} Y)^κ )^(θ/κ) )^(1/θ),
                      Y = U_h(s',g) + γ_h V_h(s',g)        [κ = θ = 1: the paper's linear (6)]
    (7)  X_h(s)     = Σ_g V_h(s,g)^ζ
    (8)  U_r(s)     = −(Σ_h X_h(s)^(−ξ))^η     [proposal: −(1/ξ)(E_h (E_g V^ζ)^(−ξ))^η; same π_r for
                                                 uniform weights, since π_r is invariant under scaling U_r]
    (9)  V_r(s)     = U_r(s) + E_{a_r∼π_r(s)} Q_r(s,a_r)

Alternative to (6')+(7) (owner, 2026-11-13; "trajectory goals", no goal dimension, X_h = 2^{P_h}):

    (7T) X_h(s) = 1 + γ_h Σ_{s'} max_{a_h} P(s'|s,a_h,π_-h,π_r)^ζ X_h(s')     (discount: owner, 2026-11-13)

With M_π(s,s') = max_{a_h} P(s'|s,a_h,π_-h,π_r(s))^ζ ≥ 0: X = 1 + γ_h M_π X.  Row sums of M_π are
≤ m := min(|A_h|, |S|) for ζ ≥ 1 (each entry ≤ 1; and p^ζ ≤ p), and can exceed 1.  Acyclicity is an
optional extra condition (then M_π is nilpotent and X exists for every γ_h).

Bracketing of (6') is reading R1 of the PDF (owner has not objected).

**Abstract form** (finite S, A nonempty, H, G; K(s,a,s') ≥ 0 with row sums ≤ 1; real β, γ_r):
an evaluation operator Φ (π, v) ↦ Φ π v ∈ ℝ^{H×G×S} with admissible set D ⊆ ℝ^{H×G×S}, and an aggregation Ψ_s : ℝ^{H×G} → ℝ.
A **solution** is (π, Q, Ve, Vr) with, for all s, a:

    s non-terminal:  Q(s,a) < 0,  π(s)(a) = (−Q(s,a))^(−β) / Σ_b (−Q(s,b))^(−β)
    s terminal:      π(s)(a) = 1/|A|   (convention; then Q(s,·) = 0 and Vr(s) = U(s))
    Ve ∈ D,  Ve = Φ π Ve,   U(s) := Ψ_s(Ve(·,·,s)) < 0
    Vr(s) = U(s) + Σ_a π(s)(a) Q(s,a),   Q(s,a) = γ_r Σ_{s'} K(s,a,s') Vr(s')

s is **terminal** iff K(s,a,s') = 0 for all a, s'.  (Finding F4: without the terminal case no
solution exists in an acyclic game, since Q = 0 at a minimal-rank state.)  A solution forces (if A is nonempty and some state is non-terminal)
γ_r > 0 and Σ_{s'} K(s,a,s') > 0 for every action of a non-terminal state.

UniqEval(Φ): for every π there is at most one Ve ∈ D with Ve = Φ π Ve (π ranging over families of distributions).
Local(Φ, ρ): (Φ π v)(h,g,s) depends on π only through π(s) and on v only through states of rank < ρ(s).
Instances: linear Φ (paper's (6)) with Ψ from (7)–(8) (meaningful for Ve > 0; the SYS-L theorems hold for any D); trajectory Φ (7T) with
Ψ_s(w) = −(Σ_h w_h^(−ξ))^η and D = {v > 0}; power-mean Φ ((6'), later batch).
Simplifications: state-independent action set, one goal set for all humans.
§1 and §4 below concern the proposal's variant of eq. (2) (U_r(s) inside Q_r(s,a)) and are **not**
about the target system (finding F1).

With x = −Q, c = −U > 0:  x(s,a) = γ_r Σ_{s'} K(s,a,s') [ c(s') + w_β(x(s',·)) ]  (w_β: §2),
i.e. x = c' + γ_r M(x) as in §3 with c' = γ_r K c.

All **L** items of this section: `EmpoHomotopy/System.lean` at commit d2dda7a, non-author statement
audit passed 2026-11-13 (after the F4 rework).

- **SYS-1 (robot side determined by U for β ≤ 1).** [**L** `sys1`] Let β ∈ [0,1].  Two solutions with the same
  U have the same Q, π and Vr; under UniqEval(Φ) also the same Ve.
- **SYS-2 (β = 0).** [**L** `sys2`] If β = 0 and UniqEval(Φ), there is at most one solution.
- **SYS-3 (acyclic).** [**L** `sys3`] If ρ : S → ℕ satisfies ρ(s') < ρ(s) whenever K(s,a,s') > 0, and Local(Φ, ρ),
  there is at most one solution, for all real β, γ_r.
- **SYS-W (non-vacuity).** [**L** `sys3_nonvacuous`, `sys1_nonvacuous`; trivial exponents ζ=ξ=η=1,
  action-independent kernels] There is an acyclic instance with a terminal state (two states) satisfying
  the hypotheses of SYS-3 that has a solution; likewise a cyclic one-state instance for SYS-1/2.
- **SYS-L (linear instance).** [**L** `sys_linear_uniqEval`, `sys_linear_local`] Φ π v h g s = Σ_a π(s)(a)[r(h,g,s,a) + γ_h Σ_{s'} Kh(h,g,s,a,s') v(h,g,s')]
  with Kh ≥ 0, row sums ≤ 1: UniqEval if γ_h ∈ [0,1); Local(Φ, ρ) if Kh respects ρ.
- **SYS-T (trajectory instance).** [**L** `sys_T_uniqEval`] G = {*}, D = {v > 0}, Φ π v h s = 1 + Σ_{s'} M_π(h,s,s') v(h,s') with
  M_π ≥ 0 arbitrary: UniqEval holds, with no row-sum or discount hypothesis (BEL-1 with c = 1, γ = 1).
  So for (7T), SYS-1 and SYS-2 hold without evaluation, row-sum or discount hypotheses
  [**L** `sys1_traj`, `sys2_traj`; they assume M_π ≥ 0 for every real π, so the concrete M_π must be
  defined (e.g. as 0) off the distributions — harmless, since solution policies are distributions].
  Concrete matrix M(s,s') = max_a P(s,a,s')^ζ, ζ ≥ 1, P substochastic: M ≥ 0, entries ≤ 1, row sums
  ≤ |A_h| and ≤ |S| [**L** `trajM_rowsum_le`, `trajM_le_one`].  **I**: that P is the kernel averaged
  over π_r(s) and the other humans; `trajΨ` is a definition without theorems.
- **SYS-TE (existence for (7T) with small discount).** Per matrix [**L** `traj_exists_unique`, audited]:
  if M ≥ 0 has row sums ≤ m and γ_h m < 1, there is exactly one real X with X = 1 + γ_h M X, and
  1 ≤ X ≤ 1/(1 − γ_h m).  The rest is **I**:  Hence U lies in a compact
  subinterval of (−∞, 0) independent of π; if moreover γ_r ∈ (0,1) and every action of a non-terminal
  state has positive successor mass, then π ↦ power law of Q(π) is a continuous self-map of Δ(A)^S and
  a solution of the full system exists for every β (Brouwer; would be a listed published-theorem
  assumption in Lean: no Brouwer fixed-point theorem was found in the pinned Mathlib by a word search).  γ_h m < 1 is sufficient, not necessary: what is
  needed is spectral radius of γ_h M_π < 1 for all π.
- **SYS-P (?)** UniqEval for the power-mean Φ of (6') in cyclic games with κ, θ < 1.  (Power means of
  order < 1 are not sup-norm nonexpansive; rewards may vanish, so BEL-1 does not apply directly.)
- **SYS-6 (non-uniqueness in a cyclic game).** [**L** `sys6_two_solutions`, `sys6_three_solutions`,
  `EmpoHomotopy/NonUnique.lean`, commit c4556d0, audited] S = {0,1}, A = {a0,a1,a2},
  one human, one goal, linear Φ, Ψ from (7)–(8); state 0: all actions lead to 0 with reward 1/20;
  state 1: a0, a1 lead to 0 (reward 1/20), a2 leads to 1 (reward 1); γ_h = 2/3, γ_r = 4/5, ζ = 2, ξ = 1,
  η = 3, β = 2.  With p = π(1)(a2), solutions correspond to zeros of a rational function g on (0,1),
  and g(1/2) < 0 < g(3/5), g(19/20) > 0 > g(99/100), g changes sign on [1−10⁻¹⁵, 1−10⁻¹⁶]: at least three
  solutions with pairwise distinct π (p ≈ 0.546, 0.954, ≈ 1).  The instance has no terminal state
  and β = 2 > 1, so SYS-1..3 do not apply.
- **SYS-N (N; `numerics/cyclic/REPORT.md`).** Random small cyclic games, multi-start + arclength:
  linear V_h: 23 of 229 instances with ≥ 2 solutions, none at β ≤ 1 (smallest fold β ≈ 1.09);
  power-mean V_h: 9 of 74, none at β ≤ 1, V_h iteration always converged to one limit (sampled);
  trajectory form (7T): 53 of 168, one instance with 3 solutions for β ≈ 0.95–1.2.  Warm-start Newton
  stalls at folds, arclength passes them; tracing in γ_r from ≈ 0 reached a different solution
  (near-deterministic) than tracing in β from 0 (near-uniform) on the simplest instance.
- **SYS-S (N; solver, `solver/README.md`).** On the SYS-6 instance the three solutions at β = 2 lie on
  one connected curve from β = 0 (folds at β ≈ 2.586 and β ≈ 1.139).  Selection: β-continuation from 0
  (first crossing) → p ≈ 0.546; γ_r-continuation from ≈ 0 → p ≈ 1; finite-horizon unrolling → p ≈ 1
  (T = 147); multistart → all three.  On 72 random cyclic games (β = 1.5, 4) all methods agreed on one
  solution.
- **SYS-4 (?)** Existence of a solution (positivity conditions on the data; paper: ε-regularisation).
- **SYS-5 (?)** Is the solution unique in cyclic games for β ≤ 1 with linear or power-mean V_h?
  (Not for (7T), per SYS-N.)
- Remark (**I**): π_r is invariant under scaling Q_r, so γ_r → 0 is not trivial: with x̃ = x/γ_r,
  x̃ = K(c + γ_r w_β(x̃)); at γ_r = 0, π_r(s) ∝ (Σ_{s'}K(s,a,s') c(s'))^(−β) still feeds back through c.

## 1. Local problem (proposal's variant only; one state, continuation costs d given)

All **L** items: Lean names in `EmpoHomotopy/`, non-author statement audit passed 2026-11-13
(`protocol/REVIEW_LEDGER.md`).

Data: finite nonempty A; d : A → [0,∞); u : Δ(A) → (0,∞) continuous; β ≥ 0.
σ_β(x)(a) := (x+d_a)^(−β) / Σ_b (x+d_b)^(−β)  for x > 0.
A *local solution* is π ∈ Δ(A) with π = σ_β(u(π)).

- **LOC-1 (scalar reduction).** [**L** `loc1`] π ↦ u(π) is a bijection from local solutions onto
  {x > 0 : x = u(σ_β(x))}, with inverse x ↦ σ_β(x).
- **LOC-2 (existence without Brouwer).** [**L** `loc2`] A local solution exists for every real β.
  Proof: φ(x) = u(σ_β(x)) is continuous and maps [min u, max u] into itself; IVT.
- **LOC-3.** [**L** `loc3`, `loc3_beta_zero`] If d is constant (in particular if γ_r = 0), then σ_β(x) is uniform for all β, x;
  the local solution is unique and uniform.  Likewise for β = 0.
- **LOC-4 (uniqueness for small β).** [**L** `loc4`] Let 0 < m ≤ u on Δ(A), u L-Lipschitz w.r.t. ‖·‖₁,
  d_min, d_max the extreme values of d, D = d_max − d_min.  If
      β · L · D < 2 (m + d_min)(m + d_max)
  then there is at most one local solution (exactly one, with LOC-2).
  Proof: dσ_a/dx = β σ_a (r̄ − r_a), r_a = 1/(x+d_a), r̄ = Σ σ_b r_b; so
  ‖σ'(x)‖₁ = β E_σ|r − r̄| ≤ β (r_max − r_min)/2 = β D / (2 (x+d_min)(x+d_max)); φ is a contraction on [m,∞).
  **N**: the bound is very loose (first multiplicity at β ≥ 613 β* in 3666 random instances).
- **LOC-5 (N, multiplicity exists).** |A| = 2, u(π) = (π·v)^(−ξη)/ξ, v = (0.327, 0.96), d = (2.299, 0),
  ξ = 3.765, η = 3.338, β = 2: three solutions x ≈ 0.663, 1.729, 51.9 (`numerics/REPORT.md`).
  Not found in the bus toy model (12928 local problems); none found for β < 1.

## 2. Lehmer mean (the robot's value aggregation)

For x ∈ (0,∞)^A:  w_β(x) := Σ_a x_a^(1−β) / Σ_a x_a^(−β)  ( = −E_{a∼π}Q with x = −Q, π ∝ x^(−β) ).

- **LEH-1.** [**L** `leh1`, every real β] min x ≤ w_β(x) ≤ max x;  w_β(λx) = λ w_β(x) for λ > 0.
- **LEH-2.** [**L** `leh2`] For β ∈ [0,1], w_β is monotone (x ≤ y pointwise ⇒ w_β(x) ≤ w_β(y)).
- **LEH-3.** [**L** `leh3`] For β = 2, |A| = 2, w is not monotone: w(3,1) = 6/5 > 110/101 = w(10,1).
  (General β > 1: ∂w/∂x₁ < 0 for x₁/x₂ large; **I**.)

## 3. Robot-side Bellman equation given U (cyclic case allowed)

Data: finite Ω (= S×A_r), c : Ω → (0,∞), γ ≥ 0, M : (0,∞)^Ω → ℝ^Ω monotone and
positively homogeneous of degree 1.  Equation: x = c + γ M(x), x ∈ (0,∞)^Ω.
Instance (proposal's variant; for the target system see §0): c(s,a) = −U_r(s), M(x)(s,a) = Σ_{s'} T̄(s'|s,a) w_β(x(s',·)), β ∈ [0,1]
(hypotheses of BEL-1 for this instance: **L** `lehmerBellmanOp_hyps`; those of BEL-2: **I**).

- **BEL-1 (uniqueness).** [**L** `bel1`] The equation has at most one solution, for every γ ≥ 0.
  Proof: for solutions x, y let λ = max_ω x_ω/y_ω.  If λ > 1 then
  x = c + γM(x) ≤ c + γλM(y) = λy − (λ−1)c < λy pointwise, contradicting the choice of λ.
- **BEL-2 (existence).** [**L** `bel2`] If γ < 1, M monotone, M ≥ 0, continuous on (0,∞)^Ω and
  (x ≤ b pointwise ⇒ M(x) ≤ b) for all b, a solution exists (monotone iteration; homogeneity not needed).
- Corollary (**I**): for β ≤ 1, γ_r < 1, system (1)–(2) determines (Q_r, π_r) uniquely from U_r;
  the full system reduces to a fixed-point problem U = 𝒰(U) in |S| unknowns.  All
  non-uniqueness for β ≤ 1 comes from the human-side feedback (3)–(5); for β > 1 also from LEH-3.

## 4. Acyclic games in the proposal's variant  — **I**

Backward induction over states: at each s the downstream solution fixes d and the map u (from
(3)–(5), continuous under P), so LOC-2 gives existence of a solution of (1)–(5) for all β without
Brouwer, and LOC-1 reduces path-tracing in (β, π_r(s)) to a planar curve g(β,x) = x − u(σ_β(x)) = 0.

## 5. Path results — **?** (next releases)

- PATH-1: the component of {g = 0} ⊂ [0,B]×[m−ε, M+ε] containing (0, u(unif)) meets β = B
  (planar separation; published-theorem assumption candidate).
- PATH-2: g real-analytic ⇒ the zero set is locally a finite union of analytic arcs, so the
  principal branch can be traced through bifurcations without a genericity assumption.
- PATH-3: general cyclic case via Sard/transversality (Herings–Peeters 2010 framework).
