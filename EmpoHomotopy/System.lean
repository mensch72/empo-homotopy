import EmpoHomotopy.Bellman

/-!
# The target system (STATEMENTS.md §0), abstract form

Finite state set `S`, robot actions `A`, humans `H`, goals `G`.  The robot side is
`Q(s,a) = γ_r ∑_{s'} K(s,a,s') V_r(s')`, `π(s) ∝ (−Q(s,·))^(−β)`, `V_r(s) = U(s) + ∑_a π(s)(a) Q(s,a)`.
The human side is abstracted: an *evaluation* operator `Φ` with `V^e = Φ π V^e`, and an
*aggregation* `Ψ` with `U(s) = Ψ s (V^e(·,·,s))`.  The paper's linear `Φ` and its `Ψ` are given
as instances at the end of the file.
-/

open Finset

noncomputable section

namespace EmpoHomotopy

/-- Data of the abstract target system: robot kernel `K` (nonnegative, row sums `≤ 1`),
evaluation operator `Φ`, aggregation `Ψ`, admissible set `adm` (= `D` in STATEMENTS.md), and the real parameters `β`, `γ_r`. -/
structure SysData (S A H G : Type*) [Fintype S] where
  /-- robot transition kernel `K(s,a,s')` (human and goal expectations folded in) -/
  K : S → A → S → ℝ
  /-- human evaluation operator: solutions satisfy `Ve = Φ π Ve` -/
  Φ : (S → A → ℝ) → (H → G → S → ℝ) → (H → G → S → ℝ)
  /-- aggregation: `U(s) = Ψ s (Ve(·,·,s))` -/
  Ψ : S → (H → G → ℝ) → ℝ
  β : ℝ
  γr : ℝ
  /-- admissible set `D ⊆ ℝ^{H×G×S}` for `Ve` -/
  adm : Set (H → G → S → ℝ)
  K_nonneg : ∀ s a s', 0 ≤ K s a s'
  K_sum_le : ∀ s a, ∑ s', K s a s' ≤ 1

variable {S A H G : Type*} [Fintype S] [Fintype A]

namespace SysData

variable (D : SysData S A H G)

/-- `U(s) := Ψ s (Ve(·,·,s))`. -/
def U (Ve : H → G → S → ℝ) (s : S) : ℝ := D.Ψ s fun h g => Ve h g s

/-- A state `s` is **terminal** iff `K(s,a,s') = 0` for all `a, s'`. -/
def terminal (s : S) : Prop := ∀ a s', D.K s a s' = 0

/-- **Solution** of the abstract system (STATEMENTS.md §0): for non-terminal `s`,
`Q(s,a) < 0` and `π(s)(a) = (−Q(s,a))^(−β) / ∑_b (−Q(s,b))^(−β)`; for terminal `s`,
`π(s)(a) = 1/|A|`; and at all states `Ve ∈ adm`, `Ve = Φ π Ve`, `U(s) < 0`,
`Vr(s) = U(s) + ∑_a π(s)(a) Q(s,a)`, `Q(s,a) = γ_r ∑_{s'} K(s,a,s') Vr(s')`. -/
structure IsSolution (π Q : S → A → ℝ) (Ve : H → G → S → ℝ) (Vr : S → ℝ) : Prop where
  Q_neg : ∀ s, ¬ D.terminal s → ∀ a, Q s a < 0
  pi_eq : ∀ s, ¬ D.terminal s → ∀ a, π s a = (-Q s a) ^ (-D.β) / ∑ b, (-Q s b) ^ (-D.β)
  pi_terminal : ∀ s, D.terminal s → ∀ a, π s a = 1 / (Fintype.card A : ℝ)
  Ve_mem : Ve ∈ D.adm
  Ve_eq : Ve = D.Φ π Ve
  U_neg : ∀ s, D.U Ve s < 0
  Vr_eq : ∀ s, Vr s = D.U Ve s + ∑ a, π s a * Q s a
  Q_eq : ∀ s a, Q s a = D.γr * ∑ s', D.K s a s' * Vr s'

/-- **UniqEval**: for every policy `π` with `π(s) ∈ Δ(A)` for all `s`, there is at most one
`Ve ∈ adm` with `Ve = Φ π Ve`. -/
def UniqEval : Prop :=
  ∀ π : S → A → ℝ, (∀ s a, 0 ≤ π s a) → (∀ s, ∑ a, π s a = 1) →
    ∀ V W : H → G → S → ℝ, V ∈ D.adm → W ∈ D.adm → V = D.Φ π V → W = D.Φ π W → V = W

/-- **Locality** of `Φ` w.r.t. a rank `ρ`: `(Φ π v)(h,g,s)` depends on `π` only through `π(s)`
and on `v` only through the values `v(h',g',s')` with `ρ(s') < ρ(s)`. -/
def LocalEval (ρ : S → ℕ) : Prop :=
  ∀ (π π' : S → A → ℝ) (v v' : H → G → S → ℝ) (h : H) (g : G) (s : S), π s = π' s →
    (∀ h' g' s', ρ s' < ρ s → v h' g' s' = v' h' g' s') → D.Φ π v h g s = D.Φ π' v' h g s

open Classical in
/-- Auxiliary: continuation costs `c̃(s') = c(s')/2` at terminal, `c(s')` at non-terminal `s'`. -/
def ctilde (c : S → ℝ) (s : S) : ℝ := if D.terminal s then c s / 2 else c s

open Classical in
/-- Auxiliary: `x(s,a) = −Q(s,a)` at non-terminal `s`, `c(s)/2` at terminal `s`. -/
def xext (c : S → ℝ) (Q : S → A → ℝ) (p : S × A) : ℝ :=
  if D.terminal p.1 then c p.1 / 2 else -Q p.1 p.2

open Classical in
/-- Auxiliary constant term of the extended Bellman equation. -/
def cext (c : S → ℝ) (p : S × A) : ℝ :=
  if D.terminal p.1 then c p.1 / 2 else D.γr * ∑ s', D.K p.1 p.2 s' * D.ctilde c s'

end SysData

/-- `∑_a p_a q_a = −w_β(−q)` for `p ∝ (−q)^(−β)`, `q < 0`. -/
lemma sum_mul_eq_neg_lehmer {β : ℝ} {p q : A → ℝ} (hq : ∀ a, q a < 0)
    (hp : ∀ a, p a = (-q a) ^ (-β) / ∑ b, (-q b) ^ (-β)) :
    ∑ a, p a * q a = -lehmer β (fun a => -q a) := by
  have h : ∀ a, p a * q a = -((-q a) ^ (1 - β)) / ∑ b, (-q b) ^ (-β) := by
    intro a
    rw [hp, rpow_one_sub_eq (neg_pos.2 (hq a))]
    ring
  rw [Finset.sum_congr rfl fun a _ => h a, ← Finset.sum_div, Finset.sum_neg_distrib, lehmer,
    neg_div]

lemma lehmer_const [Nonempty A] (β : ℝ) {t : ℝ} (ht : 0 < t) : lehmer β (fun _ : A => t) = t :=
  le_antisymm (lehmer_le_of_le β (fun _ => ht) fun _ => le_rfl)
    (le_lehmer_of_le β (fun _ => ht) fun _ => le_rfl)

namespace SysData

variable {D : SysData S A H G} {π Q : S → A → ℝ} {Ve : H → G → S → ℝ} {Vr : S → ℝ}

lemma IsSolution.pi_nonneg (hs : D.IsSolution π Q Ve Vr) (s : S) (a : A) : 0 ≤ π s a := by
  by_cases ht : D.terminal s
  · rw [hs.pi_terminal s ht a]; positivity
  · rw [hs.pi_eq s ht a]
    exact div_nonneg (Real.rpow_nonneg (neg_pos.2 (hs.Q_neg s ht a)).le _)
      (Finset.sum_nonneg fun b _ => Real.rpow_nonneg (neg_pos.2 (hs.Q_neg s ht b)).le _)

lemma IsSolution.pi_sum [Nonempty A] (hs : D.IsSolution π Q Ve Vr) (s : S) :
    ∑ a, π s a = 1 := by
  by_cases ht : D.terminal s
  · rw [Finset.sum_congr rfl fun a _ => hs.pi_terminal s ht a, Finset.sum_const,
      Finset.card_univ, nsmul_eq_mul]
    have : (0 : ℝ) < Fintype.card A := by exact_mod_cast Fintype.card_pos
    field_simp
  · rw [Finset.sum_congr rfl fun a _ => hs.pi_eq s ht a, ← Finset.sum_div]
    exact div_self (lehmer_denom_pos D.β fun a => neg_pos.2 (hs.Q_neg s ht a)).ne'

lemma IsSolution.Q_terminal (hs : D.IsSolution π Q Ve Vr) {s : S} (ht : D.terminal s) (a : A) :
    Q s a = 0 := by
  rw [hs.Q_eq]
  simp [ht a]

lemma IsSolution.Vr_terminal (hs : D.IsSolution π Q Ve Vr) {s : S} (ht : D.terminal s) :
    Vr s = D.U Ve s := by
  rw [hs.Vr_eq]
  simp [hs.Q_terminal ht]

lemma IsSolution.Vr_nonterminal (hs : D.IsSolution π Q Ve Vr) {s : S} (ht : ¬ D.terminal s) :
    Vr s = D.U Ve s - lehmer D.β (fun b => -Q s b) := by
  rw [hs.Vr_eq, sum_mul_eq_neg_lehmer (hs.Q_neg s ht) (hs.pi_eq s ht)]
  ring

lemma IsSolution.Vr_neg [Nonempty A] (hs : D.IsSolution π Q Ve Vr) (s : S) : Vr s < 0 := by
  by_cases ht : D.terminal s
  · rw [hs.Vr_terminal ht]; exact hs.U_neg s
  · rw [hs.Vr_nonterminal ht]
    have := le_lehmer_of_le D.β (fun b => neg_pos.2 (hs.Q_neg s ht b))
      fun b => (neg_pos.2 (hs.Q_neg s ht b)).le
    linarith [hs.U_neg s]

/-- Extended Bellman equation on `S × A`: with `c = −U`,
`xext = cext + γ_r · M(xext)`, `M` the Lehmer–kernel operator. -/
lemma IsSolution.ext_eq [Nonempty A] (hs : D.IsSolution π Q Ve Vr) :
    D.xext (fun s => -D.U Ve s) Q = D.cext (fun s => -D.U Ve s) +
      D.γr • lehmerBellmanOp D.β (fun p s' => D.K p.1 p.2 s') (D.xext (fun s => -D.U Ve s) Q) := by
  funext ⟨s, a⟩
  simp only [xext, cext, Pi.add_apply, Pi.smul_apply, smul_eq_mul, lehmerBellmanOp]
  by_cases ht : D.terminal s
  · simp only [ite_eq_left ht]
    rw [Finset.sum_eq_zero (fun s' _ => by rw [ht a s', zero_mul]), mul_zero, add_zero]
  · simp only [ite_eq_right ht]
    rw [hs.Q_eq, ← mul_add, ← Finset.sum_add_distrib, ← mul_neg, ← Finset.sum_neg_distrib]
    congr 1
    refine Finset.sum_congr rfl fun s' _ => ?_
    by_cases ht' : D.terminal s'
    · simp only [ctilde, ite_eq_left ht']
      rw [hs.Vr_terminal ht', lehmer_const _ (by linarith [hs.U_neg s'])]
      ring
    · simp only [ctilde, ite_eq_right ht']
      rw [hs.Vr_nonterminal ht']
      ring

lemma IsSolution.xext_pos (hs : D.IsSolution π Q Ve Vr) (p : S × A) :
    0 < D.xext (fun s => -D.U Ve s) Q p := by
  unfold xext
  split_ifs with ht
  · linarith [hs.U_neg p.1]
  · exact neg_pos.2 (hs.Q_neg p.1 ht p.2)

/-- At a non-terminal state every action has positive mass to some successor. -/
lemma IsSolution.exists_K_pos (hs : D.IsSolution π Q Ve Vr) {s : S} (ht : ¬ D.terminal s)
    (a : A) : ∃ s', 0 < D.K s a s' := by
  by_contra hne
  have h0 : ∀ s', D.K s a s' = 0 := fun s' =>
    le_antisymm (not_lt.mp fun h => hne ⟨s', h⟩) (D.K_nonneg s a s')
  have := hs.Q_neg s ht a
  rw [hs.Q_eq] at this
  simp [h0] at this

/-- Robot side of SYS-1: same `U` and `β ∈ [0,1]` give the same `Q`. -/
lemma sys1_Q [Nonempty A] (hβ0 : 0 ≤ D.β) (hβ1 : D.β ≤ 1)
    {π₁ Q₁ π₂ Q₂ : S → A → ℝ} {Ve₁ Ve₂ : H → G → S → ℝ} {Vr₁ Vr₂ : S → ℝ}
    (h₁ : D.IsSolution π₁ Q₁ Ve₁ Vr₁) (h₂ : D.IsSolution π₂ Q₂ Ve₂ Vr₂)
    (hU : D.U Ve₁ = D.U Ve₂) : Q₁ = Q₂ := by
  by_cases hN : ∀ s, D.terminal s
  · funext s a
    rw [h₁.Q_terminal (hN s), h₂.Q_terminal (hN s)]
  obtain ⟨s₀, hs₀⟩ := not_forall.mp hN
  obtain ⟨a₀⟩ := ‹Nonempty A›
  have hγ : 0 < D.γr := by
    by_contra hne
    replace hne : D.γr ≤ 0 := not_lt.mp hne
    have h1 := h₁.Q_neg s₀ hs₀ a₀
    rw [h₁.Q_eq] at h1
    have h2 : ∑ s', D.K s₀ a₀ s' * Vr₁ s' ≤ 0 := Finset.sum_nonpos fun s' _ =>
      mul_nonpos_of_nonneg_of_nonpos (D.K_nonneg _ _ _) (h₁.Vr_neg s').le
    linarith [mul_nonneg_of_nonpos_of_nonpos hne h2]
  have hc' : ∀ p, 0 < D.cext (fun s => -D.U Ve₁ s) p := by
    rintro ⟨s, a⟩
    unfold cext
    split_ifs with ht
    · linarith [h₁.U_neg s]
    · obtain ⟨s', hs'⟩ := h₁.exists_K_pos ht a
      refine mul_pos hγ (Finset.sum_pos' (fun i _ => mul_nonneg (D.K_nonneg _ _ _) ?_)
        ⟨s', mem_univ _, mul_pos hs' ?_⟩)
      · unfold ctilde; split_ifs <;> linarith [h₁.U_neg i]
      · unfold ctilde; split_ifs <;> linarith [h₁.U_neg s']
  obtain ⟨hmono, hhom, -⟩ := lehmerBellmanOp_hyps hβ0 hβ1 (T := fun p s' => D.K p.1 p.2 s')
    (fun p s' => D.K_nonneg _ _ _)
  have e₂ := h₂.ext_eq
  have hx₂ := h₂.xext_pos
  rw [← hU] at e₂ hx₂
  have key := bel1 hc' hγ.le hmono hhom h₁.xext_pos hx₂ h₁.ext_eq e₂
  funext s a
  by_cases ht : D.terminal s
  · rw [h₁.Q_terminal ht, h₂.Q_terminal ht]
  · have := congrFun key (s, a)
    simp only [xext, ite_eq_right ht, neg_inj] at this
    exact this

/-- SYS-1 core with the conclusion on `π` and `Vr`. -/
lemma sys1_robot [Nonempty A] (hβ0 : 0 ≤ D.β) (hβ1 : D.β ≤ 1)
    {π₁ Q₁ π₂ Q₂ : S → A → ℝ} {Ve₁ Ve₂ : H → G → S → ℝ} {Vr₁ Vr₂ : S → ℝ}
    (h₁ : D.IsSolution π₁ Q₁ Ve₁ Vr₁) (h₂ : D.IsSolution π₂ Q₂ Ve₂ Vr₂)
    (hU : D.U Ve₁ = D.U Ve₂) : Q₁ = Q₂ ∧ π₁ = π₂ ∧ Vr₁ = Vr₂ := by
  have hQ : Q₁ = Q₂ := sys1_Q hβ0 hβ1 h₁ h₂ hU
  have hπ : π₁ = π₂ := by
    funext s a
    by_cases ht : D.terminal s
    · rw [h₁.pi_terminal s ht, h₂.pi_terminal s ht]
    · rw [h₁.pi_eq s ht, h₂.pi_eq s ht, hQ]
  refine ⟨hQ, hπ, ?_⟩
  funext s
  rw [h₁.Vr_eq, h₂.Vr_eq, hU, hπ, hQ]

end SysData

open SysData

/-- **SYS-1 (robot side determined by `U` for `β ≤ 1`).**  Let `A` be nonempty and `β ∈ [0,1]`.
If `(π₁,Q₁,Ve₁,Vr₁)` and `(π₂,Q₂,Ve₂,Vr₂)` are solutions of the abstract system with the same
`U` (i.e. `Ψ s (Ve₁(·,·,s)) = Ψ s (Ve₂(·,·,s))` for all `s`), then `Q₁ = Q₂`, `π₁ = π₂`,
`Vr₁ = Vr₂`; if moreover `Φ` has UniqEval, then also `Ve₁ = Ve₂`.
No sign or size condition on `γ_r` is needed (a solution with a non-terminal state forces
`γ_r > 0`). -/
theorem sys1 [Nonempty A] (D : SysData S A H G) (hβ0 : 0 ≤ D.β) (hβ1 : D.β ≤ 1)
    {π₁ Q₁ π₂ Q₂ : S → A → ℝ} {Ve₁ Ve₂ : H → G → S → ℝ} {Vr₁ Vr₂ : S → ℝ}
    (h₁ : D.IsSolution π₁ Q₁ Ve₁ Vr₁) (h₂ : D.IsSolution π₂ Q₂ Ve₂ Vr₂)
    (hU : D.U Ve₁ = D.U Ve₂) :
    Q₁ = Q₂ ∧ π₁ = π₂ ∧ Vr₁ = Vr₂ ∧ (D.UniqEval → Ve₁ = Ve₂) := by
  obtain ⟨hQ, hπ, hVr⟩ := sys1_robot hβ0 hβ1 h₁ h₂ hU
  refine ⟨hQ, hπ, hVr, fun hE => ?_⟩
  have h₂' := h₂.Ve_eq
  rw [← hπ] at h₂'
  exact hE π₁ h₁.pi_nonneg h₁.pi_sum Ve₁ Ve₂ h₁.Ve_mem h₂.Ve_mem h₁.Ve_eq h₂'

/-- **SYS-2 (`β = 0`).**  Let `A` be nonempty, `β = 0`, and let `Φ` have UniqEval.  Then the
abstract system has at most one solution `(π, Q, Ve, Vr)` (no hypothesis on `γ_r`). -/
theorem sys2 [Nonempty A] (D : SysData S A H G) (hβ : D.β = 0) (hE : D.UniqEval)
    {π₁ Q₁ π₂ Q₂ : S → A → ℝ} {Ve₁ Ve₂ : H → G → S → ℝ} {Vr₁ Vr₂ : S → ℝ}
    (h₁ : D.IsSolution π₁ Q₁ Ve₁ Vr₁) (h₂ : D.IsSolution π₂ Q₂ Ve₂ Vr₂) :
    π₁ = π₂ ∧ Q₁ = Q₂ ∧ Ve₁ = Ve₂ ∧ Vr₁ = Vr₂ := by
  have hπ : π₁ = π₂ := by
    funext s a
    by_cases ht : D.terminal s
    · rw [h₁.pi_terminal s ht, h₂.pi_terminal s ht]
    · rw [h₁.pi_eq s ht, h₂.pi_eq s ht, hβ]
      simp
  have h₂' := h₂.Ve_eq
  rw [← hπ] at h₂'
  have hVe : Ve₁ = Ve₂ := hE π₁ h₁.pi_nonneg h₁.pi_sum Ve₁ Ve₂ h₁.Ve_mem h₂.Ve_mem h₁.Ve_eq h₂'
  have hU : D.U Ve₁ = D.U Ve₂ := by rw [hVe]
  obtain ⟨hQ, -, hVr⟩ := sys1_robot (le_of_eq hβ.symm) (by rw [hβ]; norm_num) h₁ h₂ hU
  exact ⟨hπ, hQ, hVe, hVr⟩

/-- **SYS-3 (acyclic).**  Let `ρ : S → ℕ` satisfy `ρ(s') < ρ(s)` whenever `K(s,a,s') > 0`, and
let `Φ` be local w.r.t. `ρ` (`(Φ π v)(h,g,s)` depends on `π` only through `π(s)` and on `v`
only through `v(h',g',s')` with `ρ(s') < ρ(s)`).  Then the abstract system has at most one
solution, for every real `β` and `γ_r` and every aggregation `Ψ`. -/
theorem sys3 (D : SysData S A H G) (ρ : S → ℕ) (hρ : ∀ s a s', 0 < D.K s a s' → ρ s' < ρ s)
    (hΦ : D.LocalEval ρ)
    {π₁ Q₁ π₂ Q₂ : S → A → ℝ} {Ve₁ Ve₂ : H → G → S → ℝ} {Vr₁ Vr₂ : S → ℝ}
    (h₁ : D.IsSolution π₁ Q₁ Ve₁ Vr₁) (h₂ : D.IsSolution π₂ Q₂ Ve₂ Vr₂) :
    π₁ = π₂ ∧ Q₁ = Q₂ ∧ Ve₁ = Ve₂ ∧ Vr₁ = Vr₂ := by
  have key : ∀ n s, ρ s = n → (∀ a, Q₁ s a = Q₂ s a) ∧ π₁ s = π₂ s ∧
      (∀ h g, Ve₁ h g s = Ve₂ h g s) ∧ Vr₁ s = Vr₂ s := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
    intro s hs
    have low : ∀ s', ρ s' < ρ s → (∀ a, Q₁ s' a = Q₂ s' a) ∧ π₁ s' = π₂ s' ∧
        (∀ h g, Ve₁ h g s' = Ve₂ h g s') ∧ Vr₁ s' = Vr₂ s' :=
      fun s' h => ih (ρ s') (by omega) s' rfl
    have hQ : ∀ a, Q₁ s a = Q₂ s a := by
      intro a
      rw [h₁.Q_eq s a, h₂.Q_eq s a]
      congr 1
      refine Finset.sum_congr rfl fun s' _ => ?_
      rcases (D.K_nonneg s a s').eq_or_lt with h0 | hpos
      · rw [← h0, zero_mul, zero_mul]
      · rw [(low s' (hρ s a s' hpos)).2.2.2]
    have hπ : π₁ s = π₂ s := by
      funext a
      by_cases ht : D.terminal s
      · rw [h₁.pi_terminal s ht, h₂.pi_terminal s ht]
      · rw [h₁.pi_eq s ht a, h₂.pi_eq s ht a]
        simp only [hQ]
    have hVe : ∀ h g, Ve₁ h g s = Ve₂ h g s := by
      intro h g
      rw [h₁.Ve_eq, h₂.Ve_eq]
      exact hΦ π₁ π₂ Ve₁ Ve₂ h g s hπ fun h' g' s' hs' => (low s' hs').2.2.1 h' g'
    have hU : D.U Ve₁ s = D.U Ve₂ s := by
      simp only [SysData.U, hVe]
    have hVr : Vr₁ s = Vr₂ s := by
      rw [h₁.Vr_eq, h₂.Vr_eq, hU, hπ]
      simp only [hQ]
    exact ⟨hQ, hπ, hVe, hVr⟩
  refine ⟨funext fun s => (key _ s rfl).2.1, funext fun s => funext (key _ s rfl).1,
    funext fun h => funext fun g => funext fun s => (key _ s rfl).2.2.1 h g,
    funext fun s => (key _ s rfl).2.2.2⟩

/-! ## Instances: the paper's linear evaluation and its aggregation -/

/-- Sup-norm contraction: if `δ = γ P δ` with `P(s,s') = ∑_a p(s,a) k(s,a,s')` substochastic
and `0 ≤ γ < 1`, then `δ = 0`. -/
lemma eq_zero_of_contraction {S A : Type*} [Fintype S] [Fintype A] {γ : ℝ} (hγ0 : 0 ≤ γ)
    (hγ1 : γ < 1) {p : S → A → ℝ} (hp0 : ∀ s a, 0 ≤ p s a) (hp1 : ∀ s, ∑ a, p s a = 1)
    {k : S → A → S → ℝ} (hk0 : ∀ s a s', 0 ≤ k s a s') (hk1 : ∀ s a, ∑ s', k s a s' ≤ 1)
    {δ : S → ℝ} (hδ : ∀ s, δ s = ∑ a, p s a * (γ * ∑ s', k s a s' * δ s')) (s : S) :
    δ s = 0 := by
  have : Nonempty S := ⟨s⟩
  obtain ⟨s₀, hs₀⟩ := Finite.exists_max fun s => |δ s|
  set m := |δ s₀| with hm_def
  have hm0 : 0 ≤ m := abs_nonneg _
  have hbound : ∀ s, |δ s| ≤ γ * m := by
    intro s
    rw [hδ s]
    calc |∑ a, p s a * (γ * ∑ s', k s a s' * δ s')|
        ≤ ∑ a, |p s a * (γ * ∑ s', k s a s' * δ s')| := abs_sum_le_sum_abs _ _
      _ ≤ ∑ a, p s a * (γ * m) := by
        refine Finset.sum_le_sum fun a _ => ?_
        rw [abs_mul, abs_of_nonneg (hp0 s a), abs_mul, abs_of_nonneg hγ0]
        refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ hγ0) (hp0 s a)
        calc |∑ s', k s a s' * δ s'| ≤ ∑ s', |k s a s' * δ s'| := abs_sum_le_sum_abs _ _
          _ ≤ ∑ s', k s a s' * m := by
            refine Finset.sum_le_sum fun s' _ => ?_
            rw [abs_mul, abs_of_nonneg (hk0 s a s')]
            exact mul_le_mul_of_nonneg_left (hs₀ s') (hk0 s a s')
          _ = (∑ s', k s a s') * m := by rw [Finset.sum_mul]
          _ ≤ 1 * m := mul_le_mul_of_nonneg_right (hk1 s a) hm0
          _ = m := one_mul m
      _ = γ * m := by rw [← Finset.sum_mul, hp1, one_mul]
  have hm : m ≤ 0 := by
    have := hbound s₀
    nlinarith
  exact abs_nonpos_iff.mp ((hs₀ s).trans hm)

/-- The paper's linear evaluation operator (eq. (6), abstract form):
`(Φ π v)(h,g,s) = ∑_a π(s)(a) [ r(h,g,s,a) + γ_h ∑_{s'} Kh(h,g,s,a,s') v(h,g,s') ]`. -/
def linearΦ {S A H G : Type*} [Fintype S] [Fintype A] (r : H → G → S → A → ℝ) (γh : ℝ)
    (Kh : H → G → S → A → S → ℝ) (π : S → A → ℝ) (v : H → G → S → ℝ) : H → G → S → ℝ :=
  fun h g s => ∑ a, π s a * (r h g s a + γh * ∑ s', Kh h g s a s' * v h g s')

/-- **Instance (a), UniqEval.**  If `γ_h ∈ [0,1)` and `Kh ≥ 0` with row sums `≤ 1`, the linear
evaluation `linearΦ r γ_h Kh` has UniqEval: for every `π` with `π(s) ∈ Δ(A)` there is at most
one `v` with `v = linearΦ r γ_h Kh π v` (any real `r`; any admissible set, e.g. `univ`). -/
theorem sys_linear_uniqEval (D : SysData S A H G) {r : H → G → S → A → ℝ} {γh : ℝ}
    {Kh : H → G → S → A → S → ℝ} (hΦ : D.Φ = linearΦ r γh Kh) (hγ0 : 0 ≤ γh) (hγ1 : γh < 1)
    (hKh0 : ∀ h g s a s', 0 ≤ Kh h g s a s') (hKh1 : ∀ h g s a, ∑ s', Kh h g s a s' ≤ 1) :
    D.UniqEval := by
  intro π hπ0 hπ1 V W _ _ hV hW
  rw [hΦ] at hV hW
  funext h g s
  have hδ : ∀ s, V h g s - W h g s =
      ∑ a, π s a * (γh * ∑ s', Kh h g s a s' * (V h g s' - W h g s')) := by
    intro s
    conv_lhs => rw [hV, hW]
    simp only [linearΦ, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    simp only [mul_sub, Finset.sum_sub_distrib]
    ring
  exact sub_eq_zero.mp
    (eq_zero_of_contraction hγ0 hγ1 hπ0 hπ1 (hKh0 h g) (hKh1 h g) hδ s)

/-- **Instance (a), locality.**  If `Kh ≥ 0` and `ρ(s') < ρ(s)` whenever
`Kh(h,g,s,a,s') > 0`, the linear evaluation `linearΦ r γ_h Kh` is local w.r.t. `ρ`. -/
theorem sys_linear_local (D : SysData S A H G) {r : H → G → S → A → ℝ} {γh : ℝ}
    {Kh : H → G → S → A → S → ℝ} (hΦ : D.Φ = linearΦ r γh Kh)
    (hKh0 : ∀ h g s a s', 0 ≤ Kh h g s a s') (ρ : S → ℕ)
    (hρ : ∀ h g s a s', 0 < Kh h g s a s' → ρ s' < ρ s) : D.LocalEval ρ := by
  intro π π' v v' h g s hπ hv
  rw [hΦ]
  simp only [linearΦ, hπ]
  have hin : ∀ a, ∑ s', Kh h g s a s' * v h g s' = ∑ s', Kh h g s a s' * v' h g s' := by
    intro a
    refine Finset.sum_congr rfl fun s' _ => ?_
    rcases (hKh0 h g s a s').eq_or_lt with h0 | hpos
    · rw [← h0, zero_mul, zero_mul]
    · rw [hv h g s' (hρ h g s a s' hpos)]
  simp only [hin]

/-- The trajectory evaluation operator (eq. (7T), abstract form), with goal set `Unit`:
`(Φ π v)(h,*,s) = 1 + ∑_{s'} M_π(h,s,s') v(h,*,s')`. -/
def trajΦ {S A H : Type*} [Fintype S] (Mπ : (S → A → ℝ) → H → S → S → ℝ) (π : S → A → ℝ)
    (v : H → Unit → S → ℝ) : H → Unit → S → ℝ :=
  fun h g s => 1 + ∑ s', Mπ π h s s' * v h g s'

/-- **SYS-T (trajectory instance).**  Let `G = Unit`, admissible set `{v | v > 0}`, and
`Φ π v h * s = 1 + ∑_{s'} M_π(h,s,s') v(h,*,s')` with `M_π(h,s,s') ≥ 0` for all `π, h, s, s'`.
Then UniqEval holds: for every `π` there is at most one positive `v` with `v = Φ π v`
(no row-sum or discount hypothesis; BEL-1 with `c = 1`, `γ = 1`). -/
theorem sys_T_uniqEval (D : SysData S A H Unit) {Mπ : (S → A → ℝ) → H → S → S → ℝ}
    (hM : ∀ π h s s', 0 ≤ Mπ π h s s') (hΦ : D.Φ = trajΦ Mπ)
    (hadm : D.adm = {v | ∀ h g s, 0 < v h g s}) : D.UniqEval := by
  intro π _ _ V W hVm hWm hV hW
  rw [hadm] at hVm hWm
  funext h g s
  let M : (S → ℝ) → (S → ℝ) := fun x s => ∑ s', Mπ π h s s' * x s'
  have hmono : ∀ x y : S → ℝ, (∀ ω, 0 < x ω) → (∀ ω, x ω ≤ y ω) → ∀ ω, M x ω ≤ M y ω :=
    fun x y _ hxy ω => Finset.sum_le_sum fun s' _ =>
      mul_le_mul_of_nonneg_left (hxy s') (hM π h ω s')
  have hhom : ∀ l : ℝ, 0 < l → ∀ x : S → ℝ, (∀ ω, 0 < x ω) → M (l • x) = l • M x := by
    intro l _ x _
    funext ω
    simp only [M, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun s' _ => by ring
  have hfix : ∀ X : H → Unit → S → ℝ, X = trajΦ Mπ π X →
      (fun s => X h g s) = 1 + (1 : ℝ) • M (fun s => X h g s) := by
    intro X hX
    funext s
    have := congrFun (congrFun (congrFun hX h) g) s
    simp only [Pi.add_apply, Pi.one_apply, one_smul, M]
    exact this
  rw [hΦ] at hV hW
  have := bel1 (c := 1) (fun _ => one_pos) zero_le_one hmono hhom (fun s => hVm h g s)
    (fun s => hWm h g s) (hfix V hV) (hfix W hW)
  exact congrFun this s

/-- The paper's aggregation (eqs. (7)–(8)):
`Ψ s w = −(∑_h (∑_g w(h,g)^ζ)^(−ξ))^η`. -/
def paperΨ {S H G : Type*} [Fintype H] [Fintype G] (ζ ξ η : ℝ) (_s : S) (w : H → G → ℝ) : ℝ :=
  -(∑ h, (∑ g, w h g ^ ζ) ^ (-ξ)) ^ η

/-- **Instance (b).**  If `H` is nonempty and `∑_g w(h,g)^ζ > 0` for every `h`, then
`paperΨ ζ ξ η s w < 0` (for all real `ζ, ξ, η`). -/
theorem sys_paper_psi_neg {S H G : Type*} [Fintype H] [Fintype G] [Nonempty H] (ζ ξ η : ℝ)
    (s : S) {w : H → G → ℝ} (hw : ∀ h, 0 < ∑ g, w h g ^ ζ) : paperΨ ζ ξ η s w < 0 := by
  unfold paperΨ
  refine neg_neg_of_pos (Real.rpow_pos_of_pos ?_ _)
  exact Finset.sum_pos (fun h _ => Real.rpow_pos_of_pos (hw h) _) univ_nonempty

/-- The trajectory aggregation (eq. (8) with `X_h` from (7T)), goal set `Unit`:
`Ψ s w = −(∑_h w(h,*)^(−ξ))^η`. -/
def trajΨ {S H : Type*} [Fintype H] (ξ η : ℝ) (_s : S) (w : H → Unit → ℝ) : ℝ :=
  -(∑ h, w h () ^ (-ξ)) ^ η

/-! ## Non-vacuity witnesses (SYS-W) -/

/-- Kernel of the acyclic witness: state `0` moves to state `1` under both actions;
state `1` is terminal. -/
def wK3 : Fin 2 → Fin 2 → Fin 2 → ℝ := fun s _ s' => if s = 0 ∧ s' = 1 then 1 else 0

/-- Acyclic witness data: `S = A = Fin 2`, `H = G = Unit`, linear `Φ` with reward `1`,
`γ_h = 1`, `Kh = K`; `Ψ = paperΨ 1 1 1`; `β = 1`, `γ_r = 1/2`, admissible set `univ`. -/
def wD3 : SysData (Fin 2) (Fin 2) Unit Unit where
  K := wK3
  Φ := linearΦ (fun _ _ _ _ => 1) 1 (fun _ _ => wK3)
  Ψ := paperΨ 1 1 1
  β := 1
  γr := 1 / 2
  adm := Set.univ
  K_nonneg := by intro s a s'; unfold wK3; split_ifs <;> norm_num
  K_sum_le := by intro s a; fin_cases s <;> simp [wK3]

lemma wK3_rank (s a s' : Fin 2) (h : 0 < wK3 s a s') :
    (fun s : Fin 2 => if s = 0 then 1 else 0) s' < (fun s : Fin 2 => if s = 0 then 1 else 0) s := by
  fin_cases s <;> fin_cases s' <;> simp [wK3] at h ⊢

/-- **SYS-W (acyclic).**  There is an instance with `S = Fin 2` (state `0 → 1`, state `1`
terminal, state `0` not terminal), a rank `ρ` with `K(s,a,s') > 0 ⇒ ρ(s') < ρ(s)`, a linear
evaluation `Φ` (reward `1`, `γ_h = 1`) local w.r.t. `ρ`, `Ψ = paperΨ 1 1 1`, `β = 1`,
`γ_r = 1/2`, which has a solution; so the hypotheses of `sys3` are satisfiable. -/
theorem sys3_nonvacuous : ∃ D : SysData (Fin 2) (Fin 2) Unit Unit, ∃ ρ : Fin 2 → ℕ,
    (∀ s a s', 0 < D.K s a s' → ρ s' < ρ s) ∧ D.LocalEval ρ ∧ D.terminal 1 ∧ ¬ D.terminal 0 ∧
    ∃ π Q Ve Vr, D.IsSolution π Q Ve Vr := by
  have ht1 : wD3.terminal 1 := by intro a s'; simp [wD3, wK3]
  have ht0 : ¬ wD3.terminal 0 := by intro h; have := h 0 1; simp [wD3, wK3] at this
  refine ⟨wD3, fun s => if s = 0 then 1 else 0, wK3_rank, ?_, ht1, ht0,
    fun _ _ => 1 / 2, fun s _ => if s = 0 then -1 / 2 else 0,
    fun _ _ s => if s = 0 then 2 else 1, fun _ => -1, ?_⟩
  · exact sys_linear_local wD3 (r := fun _ _ _ _ => 1) (γh := 1) (Kh := fun _ _ => wK3) rfl
      (fun _ _ s a s' => wD3.K_nonneg s a s') _
      fun _ _ s a s' h => wK3_rank s a s' h
  constructor
  · intro s ht a
    fin_cases s
    · norm_num
    · exact absurd ht1 ht
  · intro s ht a
    fin_cases s
    · norm_num [wD3, Fin.sum_univ_two, Real.rpow_neg_one]
    · exact absurd ht1 ht
  · intro s _ a
    simp
  · exact Set.mem_univ _
  · funext h g s
    fin_cases s <;> norm_num [wD3, linearΦ, wK3, Fin.sum_univ_two]
  · intro s
    fin_cases s <;> norm_num [SysData.U, wD3, paperΨ]
  · intro s
    fin_cases s <;> norm_num [SysData.U, wD3, paperΨ, Fin.sum_univ_two]
  · intro s a
    fin_cases s <;> norm_num [wD3, wK3, Fin.sum_univ_two]

/-- Cyclic witness data: `S = H = G = Unit`, `A = Fin 2`, self-loop `K = 1`, linear `Φ` with
reward `1`, `γ_h = 1/2`, `Kh = 1`; `Ψ = paperΨ 1 1 1`; `β = 0`, `γ_r = 1/2`, admissible set
`univ`. -/
def wD1 : SysData Unit (Fin 2) Unit Unit where
  K := fun _ _ _ => 1
  Φ := linearΦ (fun _ _ _ _ => 1) (1 / 2) (fun _ _ _ _ _ => 1)
  Ψ := paperΨ 1 1 1
  β := 0
  γr := 1 / 2
  adm := Set.univ
  K_nonneg := by intros; norm_num
  K_sum_le := by intros; simp

/-- **SYS-W (cyclic).**  There is a one-state instance with a self-loop (`K > 0`), `β = 0`
(so `β ∈ [0,1]`), a linear evaluation `Φ` (reward `1`, `γ_h = 1/2`) with UniqEval,
`Ψ = paperΨ 1 1 1`, `γ_r = 1/2`, which has a solution; so the hypotheses of `sys1` and
`sys2` are satisfiable. -/
theorem sys1_nonvacuous : ∃ D : SysData Unit (Fin 2) Unit Unit,
    D.β = 0 ∧ 0 ≤ D.β ∧ D.β ≤ 1 ∧ D.UniqEval ∧ (∀ s a s', 0 < D.K s a s') ∧
    ∃ π Q Ve Vr, D.IsSolution π Q Ve Vr := by
  have hnt : ∀ s, ¬ wD1.terminal s := by intro s h; have := h 0 (); simp [wD1] at this
  refine ⟨wD1, rfl, le_rfl, by norm_num [wD1], ?_, fun _ _ _ => by norm_num [wD1],
    fun _ _ => 1 / 2, fun _ _ => -1 / 2, fun _ _ _ => 2, fun _ => -1, ?_⟩
  · exact sys_linear_uniqEval wD1 (r := fun _ _ _ _ => 1) (γh := 1 / 2)
      (Kh := fun _ _ _ _ _ => 1) rfl (by norm_num) (by norm_num) (fun _ _ _ _ _ => zero_le_one)
      fun _ _ _ _ => by simp
  constructor
  · intro s _ a; norm_num
  · intro s _ a; norm_num [wD1, Fin.sum_univ_two]
  · intro s ht; exact absurd ht (hnt s)
  · exact Set.mem_univ _
  · funext h g s
    norm_num [wD1, linearΦ, Fin.sum_univ_two]
  · intro s
    norm_num [SysData.U, wD1, paperΨ]
  · intro s
    norm_num [SysData.U, wD1, paperΨ, Fin.sum_univ_two]
  · intro s a
    norm_num [wD1]

end EmpoHomotopy
