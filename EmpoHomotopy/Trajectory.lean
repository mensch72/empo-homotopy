import EmpoHomotopy.System

/-!
# The discounted trajectory-goal form (7T) (STATEMENTS.md §0, SYS-T, SYS-TE)

`X = 1 + γ M X` with `M ≥ 0`: existence, uniqueness and bounds for `γ m < 1` (TRJ-1);
the concrete matrix `M(s,s') = max_a P(s,a,s')^ζ` and its row sums (TRJ-2);
SYS-1/SYS-2 for the trajectory instance without an evaluation hypothesis (TRJ-3).
-/

open Finset

noncomputable section

namespace EmpoHomotopy

section TRJ1

variable {S : Type*} [Fintype S]

/-- Sup-norm argument: if `δ = γ M δ` with `M ≥ 0`, row sums `≤ m`, `γ ≥ 0`, `γ m < 1`,
then `δ = 0`. -/
lemma traj_eq_zero {M : S → S → ℝ} (hM0 : ∀ s s', 0 ≤ M s s') {m : ℝ}
    (hMm : ∀ s, ∑ s', M s s' ≤ m) {γ : ℝ} (hγ0 : 0 ≤ γ) (hγm : γ * m < 1)
    {δ : S → ℝ} (hδ : ∀ s, δ s = γ * ∑ s', M s s' * δ s') (s : S) : δ s = 0 := by
  have : Nonempty S := ⟨s⟩
  obtain ⟨s₀, hs₀⟩ := Finite.exists_max fun s => |δ s|
  set d := |δ s₀| with hd_def
  have hd0 : 0 ≤ d := abs_nonneg _
  have hbound : ∀ s, |δ s| ≤ γ * m * d := by
    intro s
    rw [hδ s, abs_mul, abs_of_nonneg hγ0, mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ hγ0
    calc |∑ s', M s s' * δ s'| ≤ ∑ s', |M s s' * δ s'| := abs_sum_le_sum_abs _ _
      _ ≤ ∑ s', M s s' * d := by
        refine Finset.sum_le_sum fun s' _ => ?_
        rw [abs_mul, abs_of_nonneg (hM0 s s')]
        exact mul_le_mul_of_nonneg_left (hs₀ s') (hM0 s s')
      _ = (∑ s', M s s') * d := by rw [Finset.sum_mul]
      _ ≤ m * d := mul_le_mul_of_nonneg_right (hMm s) hd0
  have hd : d ≤ 0 := by
    have h1 := hbound s₀
    have h2 : 0 ≤ (1 - γ * m) * d := mul_nonneg (by linarith) hd0
    nlinarith
  exact abs_nonpos_iff.mp ((hs₀ s).trans hd)

/-- Bounds for any real solution of `X = 1 + γ M X`. -/
lemma traj_bounds {M : S → S → ℝ} (hM0 : ∀ s s', 0 ≤ M s s') {m : ℝ}
    (hMm : ∀ s, ∑ s', M s s' ≤ m) {γ : ℝ} (hγ0 : 0 ≤ γ) (hγm : γ * m < 1)
    {X : S → ℝ} (hX : ∀ s, X s = 1 + γ * ∑ s', M s s' * X s') (s : S) :
    1 ≤ X s ∧ X s ≤ 1 / (1 - γ * m) := by
  have : Nonempty S := ⟨s⟩
  have hpos : 0 < 1 - γ * m := by linarith
  -- lower bound: the minimum is nonnegative
  obtain ⟨s₀, hs₀⟩ := Finite.exists_min X
  set μ := X s₀ with hμ_def
  have hlow : ∀ t, (∑ s', M t s') * μ ≤ ∑ s', M t s' * X s' := by
    intro t
    rw [Finset.sum_mul]
    exact Finset.sum_le_sum fun s' _ => mul_le_mul_of_nonneg_left (hs₀ s') (hM0 t s')
  have hμ0 : 0 ≤ μ := by
    by_contra hneg
    push_neg at hneg
    have h1 := hX s₀
    have h2 := hlow s₀
    have h3 : m * μ ≤ (∑ s', M s₀ s') * μ :=
      mul_le_mul_of_nonpos_right (hMm s₀) hneg.le
    have h4 : γ * (m * μ) ≤ γ * ∑ s', M s₀ s' * X s' :=
      mul_le_mul_of_nonneg_left (h3.trans h2) hγ0
    have h5 : μ = 1 + γ * ∑ s', M s₀ s' * X s' := h1
    nlinarith
  have hsum_nonneg : ∀ t, 0 ≤ ∑ s', M t s' * X s' := fun t =>
    Finset.sum_nonneg fun s' _ => mul_nonneg (hM0 t s') (hμ0.trans (hs₀ s'))
  refine ⟨?_, ?_⟩
  · rw [hX s]
    linarith [mul_nonneg hγ0 (hsum_nonneg s)]
  -- upper bound: the maximum `ν` satisfies `ν ≤ 1 + γ m ν`
  obtain ⟨s₁, hs₁⟩ := Finite.exists_max X
  set ν := X s₁ with hν_def
  have hν0 : 0 ≤ ν := hμ0.trans (hs₀ s₁)
  have hup : ∀ t, X t ≤ 1 + γ * (m * ν) := by
    intro t
    rw [hX t]
    have h1 : ∑ s', M t s' * X s' ≤ (∑ s', M t s') * ν := by
      rw [Finset.sum_mul]
      exact Finset.sum_le_sum fun s' _ => mul_le_mul_of_nonneg_left (hs₁ s') (hM0 t s')
    have h2 : (∑ s', M t s') * ν ≤ m * ν := mul_le_mul_of_nonneg_right (hMm t) hν0
    linarith [mul_le_mul_of_nonneg_left (h1.trans h2) hγ0]
  have hν : ν ≤ 1 / (1 - γ * m) := by
    rw [le_div_iff₀ hpos]
    have := hup s₁
    nlinarith
  exact (hs₁ s).trans hν

/-- **TRJ-1 (existence, uniqueness, bounds for (7T)).**  Let `S` be finite, `M : S × S → ℝ` with
`M ≥ 0` and all row sums `∑_{s'} M(s,s') ≤ m` (`m ≥ 0`), and `γ ≥ 0` with `γ m < 1`.  Then
there is exactly one `X ∈ ℝ^S` with `X = 1 + γ M X` (unique among all real vectors), and every
such `X` satisfies `1 ≤ X(s) ≤ 1/(1 − γ m)` for all `s`. -/
theorem traj_exists_unique (M : S → S → ℝ) (hM0 : ∀ s s', 0 ≤ M s s') {m : ℝ} (_hm0 : 0 ≤ m)
    (hMm : ∀ s, ∑ s', M s s' ≤ m) {γ : ℝ} (hγ0 : 0 ≤ γ) (hγm : γ * m < 1) :
    (∃! X : S → ℝ, ∀ s, X s = 1 + γ * ∑ s', M s s' * X s') ∧
    ∀ X : S → ℝ, (∀ s, X s = 1 + γ * ∑ s', M s s' * X s') →
      ∀ s, 1 ≤ X s ∧ X s ≤ 1 / (1 - γ * m) := by
  refine ⟨?_, fun X hX s => traj_bounds hM0 hMm hγ0 hγm hX s⟩
  -- the linear map `L x = x − γ M x` is injective, hence surjective
  let L : (S → ℝ) →ₗ[ℝ] (S → ℝ) := LinearMap.id - γ • Matrix.mulVecLin M
  have hL : ∀ x s, L x s = x s - γ * ∑ s', M s s' * x s' := by
    intro x s
    simp [L, Matrix.mulVec, dotProduct]
  have hinj : Function.Injective L := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    funext s
    refine traj_eq_zero hM0 hMm hγ0 hγm (δ := x) (fun t => ?_) s
    have := hL x t
    rw [hx] at this
    simp only [Pi.zero_apply] at this
    linarith
  obtain ⟨X, hX⟩ := (LinearMap.injective_iff_surjective.mp hinj) 1
  have hXeq : ∀ s, X s = 1 + γ * ∑ s', M s s' * X s' := by
    intro s
    have := hL X s
    rw [hX] at this
    simp only [Pi.one_apply] at this
    linarith
  refine ⟨X, hXeq, fun Y hY => funext fun s => ?_⟩
  have := traj_eq_zero hM0 hMm hγ0 hγm (δ := fun t => Y t - X t) (fun t => by
    simp only [mul_sub, Finset.sum_sub_distrib]
    rw [hY t, hXeq t]; ring) s
  linarith

end TRJ1

section TRJ2

variable {S Ah : Type*} [Fintype S] [Fintype Ah] [Nonempty Ah]

/-- The trajectory matrix of (7T): `trajM P ζ s s' = max_a P(s,a,s')^ζ` (real power). -/
def trajM (P : S → Ah → S → ℝ) (ζ : ℝ) (s s' : S) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty fun a => P s a s' ^ ζ

omit [Fintype S] in
/-- `trajM P ζ ≥ 0` when `P ≥ 0`. -/
lemma trajM_nonneg {P : S → Ah → S → ℝ} (hP0 : ∀ s a s', 0 ≤ P s a s') (ζ : ℝ) (s s' : S) :
    0 ≤ trajM P ζ s s' := by
  obtain ⟨a⟩ := ‹Nonempty Ah›
  exact (Real.rpow_nonneg (hP0 s a s') ζ).trans
    (Finset.le_sup' (fun a => P s a s' ^ ζ) (Finset.mem_univ a))

/-- `trajM P ζ s s' ≤ ∑_a P(s,a,s')^ζ`. -/
lemma trajM_le_sum {P : S → Ah → S → ℝ} (hP0 : ∀ s a s', 0 ≤ P s a s') (ζ : ℝ) (s s' : S) :
    trajM P ζ s s' ≤ ∑ a, P s a s' ^ ζ :=
  Finset.sup'_le _ _ fun a _ => Finset.single_le_sum
    (f := fun a => P s a s' ^ ζ) (fun a _ => Real.rpow_nonneg (hP0 s a s') ζ) (Finset.mem_univ a)

/-- `P(s,a,s')^ζ ≤ P(s,a,s') ≤ 1` for a substochastic `P` and `ζ ≥ 1`. -/
lemma rpow_le_P {P : S → Ah → S → ℝ} (hP0 : ∀ s a s', 0 ≤ P s a s')
    (hP1 : ∀ s a, ∑ s', P s a s' ≤ 1) {ζ : ℝ} (hζ : 1 ≤ ζ) (s : S) (a : Ah) (s' : S) :
    P s a s' ^ ζ ≤ P s a s' ∧ P s a s' ≤ 1 := by
  have hle1 : P s a s' ≤ 1 :=
    (Finset.single_le_sum (f := fun t => P s a t) (fun t _ => hP0 s a t)
      (Finset.mem_univ s')).trans (hP1 s a)
  exact ⟨Real.rpow_le_self_of_le_one (hP0 s a s') hle1 hζ, hle1⟩

/-- **TRJ-2 (row sums of the trajectory matrix).**  Let `S`, `A_h` be finite with `A_h`
nonempty, `P(s,a,s') ≥ 0` with `∑_{s'} P(s,a,s') ≤ 1`, and `ζ ≥ 1`.  Then
`M(s,s') := max_a P(s,a,s')^ζ` satisfies `M ≥ 0` and `∑_{s'} M(s,s') ≤ |A_h|` for every `s`. -/
theorem trajM_rowsum_le {P : S → Ah → S → ℝ} (hP0 : ∀ s a s', 0 ≤ P s a s')
    (hP1 : ∀ s a, ∑ s', P s a s' ≤ 1) {ζ : ℝ} (hζ : 1 ≤ ζ) :
    (∀ s s', 0 ≤ trajM P ζ s s') ∧ ∀ s, ∑ s', trajM P ζ s s' ≤ Fintype.card Ah := by
  refine ⟨trajM_nonneg hP0 ζ, fun s => ?_⟩
  calc ∑ s', trajM P ζ s s' ≤ ∑ s', ∑ a, P s a s' ^ ζ :=
        Finset.sum_le_sum fun s' _ => trajM_le_sum hP0 ζ s s'
    _ = ∑ a, ∑ s', P s a s' ^ ζ := Finset.sum_comm
    _ ≤ ∑ _a : Ah, (1 : ℝ) := Finset.sum_le_sum fun a _ =>
        (Finset.sum_le_sum fun s' _ => (rpow_le_P hP0 hP1 hζ s a s').1).trans (hP1 s a)
    _ = Fintype.card Ah := by simp

/-- **TRJ-2' (entries and row sums by `|S|`).**  Under the hypotheses of TRJ-2,
`M(s,s') ≤ 1` for all `s, s'`, hence `∑_{s'} M(s,s') ≤ |S|`. -/
theorem trajM_le_one {P : S → Ah → S → ℝ} (hP0 : ∀ s a s', 0 ≤ P s a s')
    (hP1 : ∀ s a, ∑ s', P s a s' ≤ 1) {ζ : ℝ} (hζ : 1 ≤ ζ) :
    (∀ s s', trajM P ζ s s' ≤ 1) ∧ ∀ s, ∑ s', trajM P ζ s s' ≤ Fintype.card S := by
  have h1 : ∀ s s', trajM P ζ s s' ≤ 1 := fun s s' =>
    Finset.sup'_le _ _ fun a _ =>
      let h := rpow_le_P hP0 hP1 hζ s a s'
      h.1.trans h.2
  refine ⟨h1, fun s => ?_⟩
  calc ∑ s', trajM P ζ s s' ≤ ∑ _s' : S, (1 : ℝ) := Finset.sum_le_sum fun s' _ => h1 s s'
    _ = Fintype.card S := by simp

end TRJ2

section TRJ3

variable {S A H : Type*} [Fintype S] [Fintype A]

/-- **TRJ-3a (SYS-1 for the trajectory instance).**  Let `A` be nonempty, `β ∈ [0,1]`,
`G = Unit`, admissible set `{v | v > 0}`, and `Φ = trajΦ Mπ`, i.e.
`Φ π v h * s = 1 + ∑_{s'} M_π(h,s,s') v(h,*,s')` with `M_π ≥ 0` (the human discount `γ_h ≥ 0`
is absorbed into `M_π`, e.g. `M_π = γ_h · trajM`).  Then two solutions with the same `U` have
the same `Q`, `π`, `Vr` and `Ve` (no evaluation, row-sum or discount hypothesis). -/
theorem sys1_traj [Nonempty A] (D : SysData S A H Unit) {Mπ : (S → A → ℝ) → H → S → S → ℝ}
    (hM : ∀ π h s s', 0 ≤ Mπ π h s s') (hΦ : D.Φ = trajΦ Mπ)
    (hadm : D.adm = {v | ∀ h g s, 0 < v h g s}) (hβ0 : 0 ≤ D.β) (hβ1 : D.β ≤ 1)
    {π₁ Q₁ π₂ Q₂ : S → A → ℝ} {Ve₁ Ve₂ : H → Unit → S → ℝ} {Vr₁ Vr₂ : S → ℝ}
    (h₁ : D.IsSolution π₁ Q₁ Ve₁ Vr₁) (h₂ : D.IsSolution π₂ Q₂ Ve₂ Vr₂)
    (hU : D.U Ve₁ = D.U Ve₂) :
    Q₁ = Q₂ ∧ π₁ = π₂ ∧ Vr₁ = Vr₂ ∧ Ve₁ = Ve₂ := by
  obtain ⟨hQ, hπ, hVr, hVe⟩ := sys1 D hβ0 hβ1 h₁ h₂ hU
  exact ⟨hQ, hπ, hVr, hVe (sys_T_uniqEval D hM hΦ hadm)⟩

/-- **TRJ-3b (SYS-2 for the trajectory instance).**  Let `A` be nonempty, `β = 0`, `G = Unit`,
admissible set `{v | v > 0}`, and `Φ = trajΦ Mπ` with `M_π ≥ 0` (discount absorbed into
`M_π`).  Then the abstract system has at most one solution `(π, Q, Ve, Vr)`. -/
theorem sys2_traj [Nonempty A] (D : SysData S A H Unit) {Mπ : (S → A → ℝ) → H → S → S → ℝ}
    (hM : ∀ π h s s', 0 ≤ Mπ π h s s') (hΦ : D.Φ = trajΦ Mπ)
    (hadm : D.adm = {v | ∀ h g s, 0 < v h g s}) (hβ : D.β = 0)
    {π₁ Q₁ π₂ Q₂ : S → A → ℝ} {Ve₁ Ve₂ : H → Unit → S → ℝ} {Vr₁ Vr₂ : S → ℝ}
    (h₁ : D.IsSolution π₁ Q₁ Ve₁ Vr₁) (h₂ : D.IsSolution π₂ Q₂ Ve₂ Vr₂) :
    π₁ = π₂ ∧ Q₁ = Q₂ ∧ Ve₁ = Ve₂ ∧ Vr₁ = Vr₂ :=
  sys2 D hβ (sys_T_uniqEval D hM hΦ hadm) h₁ h₂

end TRJ3

end EmpoHomotopy
