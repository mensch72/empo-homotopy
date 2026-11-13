# Statements (source of truth for targets; release 0.1 scope)

Status marks: **L** = proved in Lean (name given), **I** = informal proof only, **N** = numerical
evidence only, **?** = open.  Nothing marked I/N/? may be reported as verified.

## 0. Target system (owner decision 2026-11-13: the paper's version)

Source: arXiv:2508.00159v2, Table 2 (`tab:equations`), eqs. (4)–(9), read from the LaTeX source.
Phase 1 (human side, eqs. (1)–(3)) yields π_h independently of π_r; it is treated as exogenous here.

    (4) Q_r(s,a)    = γ_r E_g E_{a_H∼π_H(s,g)} E_{s'} V_r(s')
    (5) π_r(s)(a)   ∝ (−Q_r(s,a))^(−β_r)
    (6) V^e_h(s,g_h) = E_{g_-h} E_{a_H∼π_H(s,g)} E_{a_r∼π_r(s)} E_{s'} (U_h(s',g_h) + γ_h V^e_h(s',g_h))
    (7) X_h(s)      = Σ_{g_h} V^e_h(s,g_h)^ζ
    (8) U_r(s)      = −(Σ_h X_h(s)^(−ξ))^η
    (9) V_r(s)      = U_r(s) + E_{a_r∼π_r(s)} Q_r(s,a_r)

Abstract form used for all statements (finite S, A nonempty, H, G; real parameters):
kernels K(s,a,s') ≥ 0 and Kh(h,g,s,a,s') ≥ 0 with row sums ≤ 1 (the human and goal expectations
are folded into the kernels), rewards r(h,g,s,a) ≥ 0 (= E_{s'} U_h(s',g)).  A **solution** is
(π, Q, Ve, Vr) with, for all s, a, h, g:

    π(s) ∈ Δ(A),  Q(s,a) < 0,  π(s)(a) = (−Q(s,a))^(−β) / Σ_b (−Q(s,b))^(−β)
    Ve(h,g,s) = Σ_a π(s)(a) [ r(h,g,s,a) + γ_h Σ_{s'} Kh(h,g,s,a,s') Ve(h,g,s') ],  Ve ≥ 0
    X(h,s) := Σ_g Ve(h,g,s)^ζ > 0,   U(s) := −(Σ_h X(h,s)^(−ξ))^η
    Vr(s) = U(s) + Σ_a π(s)(a) Q(s,a),   Q(s,a) = γ_r Σ_{s'} K(s,a,s') Vr(s')

Simplifications relative to the paper: state-independent action set and one goal set G for all
humans; H nonempty.  The proposal's Table 1 differs (U_r(s) inside Q_r(s,a); extra exponents κ, θ):
§1 and §4 below concern that variant only and are **not** about the target system (finding F1).

With x = −Q, c = −U > 0:  x(s,a) = γ_r Σ_{s'} K(s,a,s') [ c(s') + w_β(x(s',·)) ]  (w_β: §2),
i.e. x = c' + γ_r M(x) as in §3 with c' = γ_r K c.

- **SYS-1 (robot side determined by U for β ≤ 1).** Let β ∈ [0,1].  Two solutions with the same
  U have the same Q, π and Vr.  If moreover γ_h ∈ [0,1), they have the same Ve.
- **SYS-2 (β = 0).** If β = 0 and γ_h, γ_r ∈ [0,1), there is at most one solution.
- **SYS-3 (acyclic).** If there is ρ : S → ℕ with ρ(s') < ρ(s) whenever K(s,a,s') > 0 or
  Kh(h,g,s,a,s') > 0, there is at most one solution, for all real β, γ_r, γ_h, ζ, ξ, η.
- **SYS-4 (?)** Existence of a solution (needs positivity conditions on the data; paper: ε-regularisation).
- **SYS-5 (?)** Is the solution unique in cyclic games for β ≤ 1?  For which β can it be non-unique?
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
