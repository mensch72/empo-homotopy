# Statements (source of truth for targets; release 0.1 scope)

Status marks: **L** = proved in Lean (name given), **I** = informal proof only, **N** = numerical
evidence only, **?** = open.  Nothing marked I/N/? may be reported as verified.

## 0. System as read from the proposal (Table 1)

Finite sets S (states), A_r (robot actions), H (humans), G (goals); transitions T(s'|s,a).
Unknown: robot policy π_r(s) ∈ Δ(A_r).  Exogenous: human policies π_h(s,g), π⁰_{-h}(s), rewards U_h ≥ 0.

    (1) π_r(s)(a) ∝ (−Q_r(s,a))^(−β),                                   β ≥ 0
    (2) Q_r(s,a) = U_r(s) + γ_r E_{a_H} E_{s'} E_{a'∼π_r(s')} Q_r(s',a') < 0
    (3) U_r(s)   = −(1/ξ) (E_h 2^(−ξ P_h(s)))^η
    (4) P_h(s)   = log2 E_g V_h(s,g)^ζ
    (5) V_h(s,g) = E_{a_h∼π_h(s,g)} ( E_{a_-h} ( E_{a_r∼π_r(s)} (E_{s'} X)^κ )^(θ/κ) )^(1/θ),
        X = U_h(s',g) + γ_h V_h(s',g)

Reading R1 (bracketing of (5)) and R2 (the first term of (2) is U_r(s), at the *current* state,
hence independent of a) are taken from the PDF as printed; both are flagged for the owner.
**Finding F1 (2026-11-13, from arXiv:2508.00159v2 Table 1, eqs. 4, 5, 9; read by a fetch agent,
not yet re-read by a second reader).**  The paper has Q_r(s,a) = γ_r E_{s'} V_r(s'),
V_r(s) = U_r(s) + E_{a∼π_r(s)} Q_r(s,a), i.e. Q_r(s,a) = γ_r E_{s'}[U_r(s') + E_{a'}Q_r(s',a')]
(reading R2').  Under R2' the term U_r(s) does not enter π_r(s), acyclic games have a unique
solution by plain backward induction (as the paper states), and §1 and §4 below are vacuous;
they matter only under R2 (the proposal as printed).  §2 and §3 hold under both readings
(under R2': c = γ_r T̄(−U_r) > 0 needs γ_r > 0 and is the same equation x = c + γ M(x)).
The paper's (6)–(8) also have no κ, θ and no log (U_r = −(Σ_h X_h^(−ξ))^η, X_h = Σ_g V^ζ).
Owner to decide which system is the target.

Standing assumption P: V_h(s,g) > 0 wherever it enters (4) (else U_r = −∞).

Consequence of R2: Q_r(s,·) depends on a only through the continuation term, while U_r(s) depends
on π_r(s) itself through (5).  Write x = −U_r(s) > 0 and d_a = −γ_r E[...Q_r(s',a')] ≥ 0.

## 1. Local problem (one state, continuation costs d given)

Data: finite nonempty A; d : A → [0,∞); u : Δ(A) → (0,∞) continuous; β ≥ 0.
σ_β(x)(a) := (x+d_a)^(−β) / Σ_b (x+d_b)^(−β)  for x > 0.
A *local solution* is π ∈ Δ(A) with π = σ_β(u(π)).

- **LOC-1 (scalar reduction).** π ↦ u(π) is a bijection from local solutions onto
  {x > 0 : x = u(σ_β(x))}, with inverse x ↦ σ_β(x).
- **LOC-2 (existence without Brouwer).** A local solution exists for every β ≥ 0.
  Proof: φ(x) = u(σ_β(x)) is continuous and maps [min u, max u] into itself; IVT.
- **LOC-3.** If d is constant (in particular if γ_r = 0), then σ_β(x) is uniform for all β, x;
  the local solution is unique and uniform.  Likewise for β = 0.
- **LOC-4 (uniqueness for small β).** Let m ≤ u ≤ M on Δ(A), u L-Lipschitz w.r.t. ‖·‖₁,
  d_min, d_max the extreme values of d, D = d_max − d_min.  If
      β · L · D < 2 (m + d_min)(m + d_max)
  then the local solution is unique.
  Proof: dσ_a/dx = β σ_a (r̄ − r_a), r_a = 1/(x+d_a), r̄ = Σ σ_b r_b; so
  ‖σ'(x)‖₁ = β E_σ|r − r̄| ≤ β (r_max − r_min)/2 = β D / (2 (x+d_min)(x+d_max)); φ is a contraction on [m,M].

## 2. Lehmer mean (the robot's value aggregation)

For x ∈ (0,∞)^A:  w_β(x) := Σ_a x_a^(1−β) / Σ_a x_a^(−β)  ( = −E_{a∼π}Q with x = −Q, π ∝ x^(−β) ).

- **LEH-1.** min x ≤ w_β(x) ≤ max x;  w_β(λx) = λ w_β(x) for λ > 0.
- **LEH-2.** For β ∈ [0,1], w_β is monotone (x ≤ y pointwise ⇒ w_β(x) ≤ w_β(y)).
- **LEH-3.** For β = 2, |A| = 2, w is not monotone: w(3,1) = 6/5 > 110/101 = w(10,1).
  (General β > 1: ∂w/∂x₁ < 0 for x₁/x₂ large; **I**.)

## 3. Robot-side Bellman equation given U (cyclic case allowed)

Data: finite Ω (= S×A_r), c : Ω → (0,∞), γ ≥ 0, M : (0,∞)^Ω → [0,∞)^Ω monotone and
positively homogeneous of degree 1.  Equation: x = c + γ M(x), x ∈ (0,∞)^Ω.
Instance: c(s,a) = −U_r(s), M(x)(s,a) = Σ_{s'} T̄(s'|s,a) w_β(x(s',·)), β ∈ [0,1] (by LEH-1,2).

- **BEL-1 (uniqueness).** The equation has at most one solution, for every γ ≥ 0.
  Proof: for solutions x, y let λ = max_ω x_ω/y_ω.  If λ > 1 then
  x = c + γM(x) ≤ c + γλM(y) = λy − (λ−1)c < λy pointwise, contradicting the choice of λ.
- **BEL-2 (existence).** If γ < 1 and M(x) ≤ max x (pointwise), M continuous, a solution exists
  (monotone iteration from x⁰ = c in the box [min c, max c/(1−γ)]).  **I**
- Corollary (**I**): for β ≤ 1, γ_r < 1, system (1)–(2) determines (Q_r, π_r) uniquely from U_r;
  the full system reduces to a fixed-point problem U = 𝒰(U) in |S| unknowns.  All
  non-uniqueness for β ≤ 1 comes from the human-side feedback (3)–(5); for β > 1 also from LEH-3.

## 4. Acyclic (finite-horizon) games  — **I**

Backward induction over states: at each s the downstream solution fixes d and the map u (from
(3)–(5), continuous under P), so LOC-2 gives existence of a solution of (1)–(5) for all β without
Brouwer, and LOC-1 reduces path-tracing in (β, π_r(s)) to a planar curve g(β,x) = x − u(σ_β(x)) = 0.

## 5. Path results — **?** (next releases)

- PATH-1: the component of {g = 0} ⊂ [0,B]×[m−ε, M+ε] containing (0, u(unif)) meets β = B
  (planar separation; published-theorem assumption candidate).
- PATH-2: g real-analytic ⇒ the zero set is locally a finite union of analytic arcs, so the
  principal branch can be traced through bifurcations without a genericity assumption.
- PATH-3: general cyclic case via Sard/transversality (Herings–Peeters 2010 framework).
