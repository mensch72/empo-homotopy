import Mathlib

/-!
# Local problem at one state (STATEMENTS.md §1)

Data: finite nonempty `A`, continuation costs `d : A → [0,∞)`, `u : Δ(A) → (0,∞)`, `β ≥ 0`.
`σ_β(x)(a) = (x + d a)^(-β) / ∑_b (x + d b)^(-β)` (`powerLawPolicy`), and a local solution is
`π ∈ Δ(A)` with `π = σ_β(u π)`.

`Δ(A)` is Mathlib's `stdSimplex ℝ A = {f | (∀ a, 0 ≤ f a) ∧ ∑ a, f a = 1}`; this set-valued
definition is deprecated upstream in favour of a `Finsupp`-based structure, so the deprecation
linter is switched off in this file.
-/

set_option linter.deprecated false

open Finset Set

noncomputable section

namespace EmpoHomotopy

variable {A : Type*} [Fintype A]

/-- The power-law policy `σ_β(x)(a) = (x + d a)^(-β) / ∑_b (x + d b)^(-β)`. -/
def powerLawPolicy (β : ℝ) (d : A → ℝ) (x : ℝ) : A → ℝ :=
  fun a => (x + d a) ^ (-β) / ∑ b, (x + d b) ^ (-β)

/-- A local solution: `π ∈ Δ(A)` with `π = σ_β(u π)`. -/
def IsLocalSolution (β : ℝ) (d : A → ℝ) (u : (A → ℝ) → ℝ) (π : A → ℝ) : Prop :=
  π ∈ stdSimplex ℝ A ∧ π = powerLawPolicy β d (u π)

variable [Nonempty A]

lemma powerLawPolicy_mem' {β : ℝ} {d : A → ℝ} {x : ℝ} (hx : ∀ a, 0 < x + d a) :
    powerLawPolicy β d x ∈ stdSimplex ℝ A := by
  have hpos : ∀ a, 0 < (x + d a) ^ (-β) := fun a => Real.rpow_pos_of_pos (hx a) _
  have hZ : 0 < ∑ b, (x + d b) ^ (-β) := sum_pos (fun b _ => hpos b) univ_nonempty
  refine ⟨fun a => div_nonneg (hpos a).le hZ.le, ?_⟩
  simp only [powerLawPolicy, ← Finset.sum_div]
  exact div_self hZ.ne'

lemma powerLawPolicy_mem {β : ℝ} {d : A → ℝ} (hd : ∀ a, 0 ≤ d a) {x : ℝ} (hx : 0 < x) :
    powerLawPolicy β d x ∈ stdSimplex ℝ A :=
  powerLawPolicy_mem' fun a => by linarith [hd a]

/-! ## LOC-1 -/

/-- **LOC-1 (scalar reduction).** Let `d ≥ 0` and let `u` be positive on `Δ(A)`.  Then
`π ↦ u(π)` is a bijection from the local solutions onto `{x > 0 : x = u(σ_β(x))}`, with inverse
`x ↦ σ_β(x)`. -/
theorem loc1 {β : ℝ} {d : A → ℝ} (hd : ∀ a, 0 ≤ d a) {u : (A → ℝ) → ℝ}
    (hu : ∀ π ∈ stdSimplex ℝ A, 0 < u π) :
    ∃ e : {π : A → ℝ // IsLocalSolution β d u π} ≃
        {x : ℝ // 0 < x ∧ x = u (powerLawPolicy β d x)},
      (∀ π, (e π : ℝ) = u π) ∧ ∀ x, (e.symm x : A → ℝ) = powerLawPolicy β d x :=
  ⟨{ toFun := fun π => ⟨u π, hu _ π.2.1, congrArg u π.2.2⟩
     invFun := fun x => ⟨powerLawPolicy β d x, powerLawPolicy_mem hd x.2.1,
       congrArg (powerLawPolicy β d) x.2.2⟩
     left_inv := fun π => Subtype.ext π.2.2.symm
     right_inv := fun x => Subtype.ext x.2.2.symm }, fun _ => rfl, fun _ => rfl⟩

/-! ## LOC-2 -/

lemma continuousOn_powerLawPolicy {β : ℝ} {d : A → ℝ} (hd : ∀ a, 0 ≤ d a) :
    ContinuousOn (powerLawPolicy β d) (Ioi 0) := by
  have hpos : ∀ x ∈ Ioi (0 : ℝ), ∀ a, 0 < x + d a := fun x hx a => by
    have : (0 : ℝ) < x := hx
    linarith [hd a]
  have hc : ∀ a, ContinuousOn (fun x : ℝ => (x + d a) ^ (-β)) (Ioi 0) := fun a =>
    (continuousOn_id.add continuousOn_const).rpow_const fun x hx => Or.inl (hpos x hx a).ne'
  refine continuousOn_pi.2 fun a => ?_
  exact (hc a).div (continuousOn_finset_sum _ fun b _ => hc b) fun x hx =>
    (sum_pos (fun b _ => Real.rpow_pos_of_pos (hpos x hx b) _) univ_nonempty).ne'

/-- **LOC-2 (existence without Brouwer).** Let `d ≥ 0` and let `u` be positive and continuous on
`Δ(A)`.  Then a local solution exists (for every real `β`, in particular every `β ≥ 0`).
Proof: `φ(x) = u(σ_β(x))` is continuous and maps `[min u, max u]` into itself; IVT. -/
theorem loc2 (β : ℝ) {d : A → ℝ} (hd : ∀ a, 0 ≤ d a) {u : (A → ℝ) → ℝ}
    (hu : ∀ π ∈ stdSimplex ℝ A, 0 < u π) (hcont : ContinuousOn u (stdSimplex ℝ A)) :
    ∃ π, IsLocalSolution β d u π := by
  have hK := isCompact_stdSimplex ℝ A
  have hne : (stdSimplex ℝ A).Nonempty := ⟨_, powerLawPolicy_mem (β := β) hd one_pos⟩
  obtain ⟨p, hp, hpmin⟩ := hK.exists_isMinOn hne hcont
  obtain ⟨q, hq, hqmax⟩ := hK.exists_isMaxOn hne hcont
  have hm : 0 < u p := hu p hp
  have hmM : u p ≤ u q := isMinOn_iff.1 hpmin q hq
  have hφ : ∀ x, 0 < x → u p ≤ u (powerLawPolicy β d x) ∧ u (powerLawPolicy β d x) ≤ u q :=
    fun x hx => ⟨isMinOn_iff.1 hpmin _ (powerLawPolicy_mem hd hx),
      isMaxOn_iff.1 hqmax _ (powerLawPolicy_mem hd hx)⟩
  have hc : ContinuousOn (fun x => x - u (powerLawPolicy β d x)) (Icc (u p) (u q)) :=
    continuousOn_id.sub (hcont.comp ((continuousOn_powerLawPolicy hd).mono
      fun x hx => (hm.trans_le hx.1 : (0 : ℝ) < x))
      fun x hx => powerLawPolicy_mem hd (hm.trans_le hx.1))
  have h0 : (0 : ℝ) ∈ Icc (u p - u (powerLawPolicy β d (u p)))
      (u q - u (powerLawPolicy β d (u q))) :=
    ⟨by linarith [(hφ _ hm).1], by linarith [(hφ _ (hm.trans_le hmM)).2]⟩
  obtain ⟨x, hx, hx0⟩ := intermediate_value_Icc hmM hc h0
  have hxpos : 0 < x := hm.trans_le hx.1
  have hfix : x = u (powerLawPolicy β d x) := by
    simp only at hx0
    linarith
  exact ⟨powerLawPolicy β d x, powerLawPolicy_mem hd hxpos, congrArg (powerLawPolicy β d) hfix⟩

/-! ## LOC-3 -/

lemma uniform_mem : (fun _ => 1 / (Fintype.card A : ℝ)) ∈ stdSimplex ℝ A := by
  have hc : (0 : ℝ) < Fintype.card A := by exact_mod_cast Fintype.card_pos
  refine ⟨fun _ => by positivity, ?_⟩
  rw [sum_const, card_univ, nsmul_eq_mul]
  field_simp

lemma powerLawPolicy_of_const {β : ℝ} {d : A → ℝ} (hdc : ∀ a b, d a = d b) {x : ℝ}
    (hx : ∀ a, 0 < x + d a) : powerLawPolicy β d x = fun _ => 1 / (Fintype.card A : ℝ) := by
  funext a
  have hc : (0 : ℝ) < Fintype.card A := by exact_mod_cast Fintype.card_pos
  have he : 0 < (x + d a) ^ (-β) := Real.rpow_pos_of_pos (hx a) _
  have hs : ∑ b, (x + d b) ^ (-β) = ∑ _b : A, (x + d a) ^ (-β) :=
    sum_congr rfl fun b _ => by rw [hdc b a]
  simp only [powerLawPolicy]
  rw [hs, sum_const, card_univ, nsmul_eq_mul]
  field_simp

omit [Nonempty A] in
lemma powerLawPolicy_zero (d : A → ℝ) (x : ℝ) :
    powerLawPolicy 0 d x = fun _ => 1 / (Fintype.card A : ℝ) := by
  funext a
  simp [powerLawPolicy]

lemma isLocalSolution_iff_uniform {β : ℝ} {d : A → ℝ} {u : (A → ℝ) → ℝ}
    (h : ∀ π ∈ stdSimplex ℝ A, powerLawPolicy β d (u π) = fun _ => 1 / (Fintype.card A : ℝ))
    (π : A → ℝ) : IsLocalSolution β d u π ↔ π = fun _ => 1 / (Fintype.card A : ℝ) := by
  constructor
  · rintro ⟨hπ, he⟩
    rw [he, h π hπ]
  · rintro rfl
    exact ⟨uniform_mem, (h _ uniform_mem).symm⟩

/-- **LOC-3 (constant continuation costs).** If `d ≥ 0` is constant and `u` is positive on
`Δ(A)`, then for every real `β` and every `x > 0` the policy `σ_β(x)` is uniform, and the local
solution is unique and uniform: `π` is a local solution iff `π = (1/|A|, …, 1/|A|)`. -/
theorem loc3 (β : ℝ) {d : A → ℝ} (hd : ∀ a, 0 ≤ d a) (hdc : ∀ a b, d a = d b)
    {u : (A → ℝ) → ℝ} (hu : ∀ π ∈ stdSimplex ℝ A, 0 < u π) :
    (∀ x, 0 < x → powerLawPolicy β d x = fun _ => 1 / (Fintype.card A : ℝ)) ∧
      ∀ π, IsLocalSolution β d u π ↔ π = fun _ => 1 / (Fintype.card A : ℝ) := by
  have h1 : ∀ x, 0 < x → powerLawPolicy β d x = fun _ => 1 / (Fintype.card A : ℝ) :=
    fun x hx => powerLawPolicy_of_const hdc fun a => by linarith [hd a]
  exact ⟨h1, isLocalSolution_iff_uniform fun π hπ => h1 _ (hu π hπ)⟩

/-- **LOC-3 (case `β = 0`).** For `β = 0`, any `d` and any `u`, `σ_0(x)` is uniform for every
`x`, and `π` is a local solution iff `π` is uniform. -/
theorem loc3_beta_zero (d : A → ℝ) (u : (A → ℝ) → ℝ) :
    (∀ x, powerLawPolicy 0 d x = fun _ => 1 / (Fintype.card A : ℝ)) ∧
      ∀ π, IsLocalSolution 0 d u π ↔ π = fun _ => 1 / (Fintype.card A : ℝ) :=
  ⟨powerLawPolicy_zero d, isLocalSolution_iff_uniform fun _ _ => powerLawPolicy_zero d _⟩

/-! ## LOC-4 -/

lemma hasDerivAt_powerLawPolicy {β : ℝ} {d : A → ℝ} {t : ℝ} (ht : ∀ a, 0 < t + d a) (a : A) :
    HasDerivAt (fun x => powerLawPolicy β d x a)
      (β * powerLawPolicy β d t a *
        (∑ b, powerLawPolicy β d t b * (t + d b)⁻¹ - (t + d a)⁻¹)) t := by
  have he : ∀ b, HasDerivAt (fun x => (x + d b) ^ (-β)) (-β * ((t + d b) ^ (-β) / (t + d b))) t := by
    intro b
    have := ((hasDerivAt_id t).add_const (d b)).rpow_const (p := -β) (Or.inl (ht b).ne')
    refine this.congr_deriv ?_
    simp only [id]
    rw [Real.rpow_sub_one (ht b).ne']
    ring
  have hZ := HasDerivAt.fun_sum (u := univ) fun b _ => he b
  have hZpos : 0 < ∑ b, (t + d b) ^ (-β) :=
    sum_pos (fun b _ => Real.rpow_pos_of_pos (ht b) _) univ_nonempty
  refine ((he a).fun_div hZ hZpos.ne').congr_deriv ?_
  symm
  set S := ∑ b, (t + d b) ^ (-β) * (t + d b)⁻¹
  have h1 : ∑ b, powerLawPolicy β d t b * (t + d b)⁻¹ = S / ∑ b, (t + d b) ^ (-β) := by
    rw [Finset.sum_div]
    exact sum_congr rfl fun b _ => by simp only [powerLawPolicy]; ring
  have h2 : ∑ b ∈ univ, -β * ((t + d b) ^ (-β) / (t + d b)) = -β * S := by
    rw [Finset.mul_sum]
    exact sum_congr rfl fun b _ => by ring
  rw [h1, h2]
  simp only [powerLawPolicy]
  have := (ht a).ne'
  field_simp
  ring

omit [Nonempty A] in
/-- `∑ wₐ |rₐ - r̄| ≤ (hi - lo)/2` for a probability vector `w` and `r ∈ [lo, hi]^A`. -/
lemma weighted_abs_dev_le {w r : A → ℝ} (hw : ∀ a, 0 ≤ w a) (hw1 : ∑ a, w a = 1) {lo hi : ℝ}
    (hr : ∀ a, lo ≤ r a ∧ r a ≤ hi) :
    ∑ a, w a * |r a - ∑ b, w b * r b| ≤ (hi - lo) / 2 := by
  set μ := ∑ b, w b * r b
  have hμlo : lo ≤ μ :=
    calc lo = ∑ b, w b * lo := by rw [← Finset.sum_mul, hw1, one_mul]
    _ ≤ μ := sum_le_sum fun b _ => mul_le_mul_of_nonneg_left (hr b).1 (hw b)
  have hμhi : μ ≤ hi :=
    calc μ ≤ ∑ b, w b * hi := sum_le_sum fun b _ => mul_le_mul_of_nonneg_left (hr b).2 (hw b)
    _ = hi := by rw [← Finset.sum_mul, hw1, one_mul]
  have hpt : ∀ a, (hi - lo) * |r a - μ| ≤
      2 * (hi - μ) * (r a - lo) - (hi - lo) * (r a - μ) := by
    intro a
    obtain ⟨h1, h2⟩ := hr a
    rcases le_total μ (r a) with h | h
    · rw [abs_of_nonneg (by linarith)]; nlinarith
    · rw [abs_of_nonpos (by linarith)]; nlinarith
  have hsum : (hi - lo) * ∑ a, w a * |r a - μ| ≤ 2 * (hi - μ) * (μ - lo) := by
    calc (hi - lo) * ∑ a, w a * |r a - μ| = ∑ a, w a * ((hi - lo) * |r a - μ|) := by
          rw [Finset.mul_sum]; exact sum_congr rfl fun a _ => by ring
    _ ≤ ∑ a, w a * (2 * (hi - μ) * (r a - lo) - (hi - lo) * (r a - μ)) :=
          sum_le_sum fun a _ => mul_le_mul_of_nonneg_left (hpt a) (hw a)
    _ = 2 * (hi - μ) * (μ - lo) := by
          have : ∀ a, w a * (2 * (hi - μ) * (r a - lo) - (hi - lo) * (r a - μ)) =
              (2 * (hi - μ) - (hi - lo)) * (w a * r a) - (2 * (hi - μ) * lo - (hi - lo) * μ) * w a :=
            fun a => by ring
          rw [sum_congr rfl fun a _ => this a, sum_sub_distrib, ← Finset.mul_sum,
            ← Finset.mul_sum, hw1]
          ring
  rcases eq_or_lt_of_le (hμlo.trans hμhi) with h | h
  · have h0 : ∀ a, |r a - μ| = 0 := fun a => by
      rw [abs_eq_zero]; linarith [hr a]
    simp only [h0, mul_zero, sum_const_zero]
    linarith
  · have h4 : 2 * (hi - μ) * (μ - lo) ≤ (hi - lo) ^ 2 / 2 := by
      nlinarith [sq_nonneg (hi + lo - 2 * μ)]
    rw [le_div_iff₀ two_pos]
    have : (hi - lo) * ((∑ a, w a * |r a - μ|) * 2) ≤ (hi - lo) * (hi - lo) := by nlinarith
    exact le_of_mul_le_mul_left this (by linarith)

lemma deriv_bound {β : ℝ} (hβ : 0 ≤ β) {d : A → ℝ} {lo hi t : ℝ} (ht : ∀ a, 0 < t + d a)
    (hlo : ∀ a, lo ≤ (t + d a)⁻¹) (hhi : ∀ a, (t + d a)⁻¹ ≤ hi) (s : A → ℝ)
    (hs : ∀ a, |s a| = 1) :
    |∑ a, s a * (β * powerLawPolicy β d t a *
        (∑ b, powerLawPolicy β d t b * (t + d b)⁻¹ - (t + d a)⁻¹))| ≤ β * ((hi - lo) / 2) := by
  obtain ⟨hσ0, hσ1⟩ := powerLawPolicy_mem' (β := β) ht
  calc _ ≤ ∑ a, |s a * (β * powerLawPolicy β d t a *
        (∑ b, powerLawPolicy β d t b * (t + d b)⁻¹ - (t + d a)⁻¹))| := abs_sum_le_sum_abs _ _
  _ = ∑ a, β * (powerLawPolicy β d t a *
        |(t + d a)⁻¹ - ∑ b, powerLawPolicy β d t b * (t + d b)⁻¹|) :=
      sum_congr rfl fun a _ => by
        rw [abs_mul, abs_mul, abs_mul, hs, abs_of_nonneg hβ, abs_of_nonneg (hσ0 a), abs_sub_comm]
        ring
  _ = β * ∑ a, powerLawPolicy β d t a *
        |(t + d a)⁻¹ - ∑ b, powerLawPolicy β d t b * (t + d b)⁻¹| := by rw [Finset.mul_sum]
  _ ≤ β * ((hi - lo) / 2) :=
      mul_le_mul_of_nonneg_left (weighted_abs_dev_le hσ0 hσ1 fun a => ⟨hlo a, hhi a⟩) hβ

/-- **LOC-4 (uniqueness for small β).** Let `β ≥ 0`, `d ≥ 0`, `d_min = min d`, `d_max = max d`,
`D = d_max - d_min`, and suppose `m ≤ u` on `Δ(A)` with `m > 0` and `u` is `L`-Lipschitz on
`Δ(A)` with respect to the ℓ¹ distance `∑ₐ |πₐ - π'ₐ|`.  If
`β · L · D < 2 (m + d_min)(m + d_max)` then there is at most one local solution. -/
theorem loc4 {β : ℝ} (hβ : 0 ≤ β) {d : A → ℝ} (hd : ∀ a, 0 ≤ d a) {u : (A → ℝ) → ℝ}
    {m L : ℝ} (hm0 : 0 < m) (hm : ∀ π ∈ stdSimplex ℝ A, m ≤ u π)
    (hL : ∀ π ∈ stdSimplex ℝ A, ∀ π' ∈ stdSimplex ℝ A,
      |u π - u π'| ≤ L * ∑ a, |π a - π' a|)
    (hsmall : β * L * (univ.sup' univ_nonempty d - univ.inf' univ_nonempty d) <
      2 * (m + univ.inf' univ_nonempty d) * (m + univ.sup' univ_nonempty d))
    {π₁ π₂ : A → ℝ} (h₁ : IsLocalSolution β d u π₁) (h₂ : IsLocalSolution β d u π₂) :
    π₁ = π₂ := by
  set dmin := univ.inf' univ_nonempty d with hdmin
  set dmax := univ.sup' univ_nonempty d with hdmax
  have hdmin_le : ∀ a, dmin ≤ d a := fun a => inf'_le _ (mem_univ a)
  have hle_dmax : ∀ a, d a ≤ dmax := fun a => le_sup' _ (mem_univ a)
  obtain ⟨a₀⟩ := ‹Nonempty A›
  have hdmin0 : 0 ≤ dmin := Finset.le_inf' _ _ fun a _ => hd a
  have hDD : dmin ≤ dmax := (hdmin_le a₀).trans (hle_dmax a₀)
  have hP : 0 < (m + dmin) * (m + dmax) := mul_pos (by linarith) (by linarith)
  set C := β * ((dmax - dmin) / ((m + dmin) * (m + dmax))) / 2 with hC
  -- `σ_β` is `C`-Lipschitz from `[m, ∞)` to `(Δ(A), ℓ¹)`.
  have hσLip : ∀ x₁ ∈ Ici m, ∀ x₂ ∈ Ici m,
      ∑ a, |powerLawPolicy β d x₁ a - powerLawPolicy β d x₂ a| ≤ C * |x₁ - x₂| := by
    intro x₁ hx₁ x₂ hx₂
    set s : A → ℝ := fun a =>
      if 0 ≤ powerLawPolicy β d x₁ a - powerLawPolicy β d x₂ a then 1 else -1 with hs_def
    have hs : ∀ a, |s a| = 1 := fun a => by
      simp only [hs_def]; split_ifs <;> simp
    have hsabs : ∀ a, s a * (powerLawPolicy β d x₁ a - powerLawPolicy β d x₂ a) =
        |powerLawPolicy β d x₁ a - powerLawPolicy β d x₂ a| := fun a => by
      simp only [hs_def]
      split_ifs with h
      · rw [one_mul, abs_of_nonneg h]
      · rw [abs_of_neg (not_le.mp h)]; ring
    have htpos : ∀ t ∈ Ici m, ∀ a, 0 < t + d a := fun t ht a => by
      have : m ≤ t := ht
      linarith [hd a]
    have hf : ∀ t ∈ Ici m, HasDerivWithinAt (fun x => ∑ a, s a * powerLawPolicy β d x a)
        (∑ a, s a * (β * powerLawPolicy β d t a *
          (∑ b, powerLawPolicy β d t b * (t + d b)⁻¹ - (t + d a)⁻¹))) (Ici m) t :=
      fun t ht => (HasDerivAt.fun_sum fun a _ =>
        (hasDerivAt_powerLawPolicy (htpos t ht) a).const_mul (s a)).hasDerivWithinAt
    have hbound : ∀ t ∈ Ici m, ‖∑ a, s a * (β * powerLawPolicy β d t a *
          (∑ b, powerLawPolicy β d t b * (t + d b)⁻¹ - (t + d a)⁻¹))‖ ≤ C := by
      intro t ht
      have hmt : m ≤ t := ht
      have ha : 0 < t + dmin := by linarith
      have hb : 0 < t + dmax := by linarith
      rw [Real.norm_eq_abs]
      refine (deriv_bound hβ (htpos t ht) (lo := (t + dmax)⁻¹) (hi := (t + dmin)⁻¹)
        (fun a => inv_anti₀ (htpos t ht a) (by linarith [hle_dmax a]))
        (fun a => inv_anti₀ ha (by linarith [hdmin_le a])) s hs).trans ?_
      have h1 : (t + dmin)⁻¹ - (t + dmax)⁻¹ = (dmax - dmin) / ((t + dmin) * (t + dmax)) := by
        field_simp
        ring
      have h2 : (dmax - dmin) / ((t + dmin) * (t + dmax)) ≤
          (dmax - dmin) / ((m + dmin) * (m + dmax)) :=
        div_le_div_of_nonneg_left (by linarith) hP
          (mul_le_mul (by linarith) (by linarith) (by linarith) (by linarith))
      rw [h1, hC]
      have := mul_le_mul_of_nonneg_left h2 hβ
      linarith
    have hmvt := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hf hbound (convex_Ici m)
      hx₂ hx₁
    rw [Real.norm_eq_abs, Real.norm_eq_abs] at hmvt
    have hfx : (∑ a, s a * powerLawPolicy β d x₁ a) - ∑ a, s a * powerLawPolicy β d x₂ a =
        ∑ a, |powerLawPolicy β d x₁ a - powerLawPolicy β d x₂ a| := by
      rw [← sum_sub_distrib]
      exact sum_congr rfl fun a _ => by rw [← hsabs a]; ring
    rw [hfx] at hmvt
    exact (le_abs_self _).trans hmvt
  obtain ⟨hs₁, he₁⟩ := h₁
  obtain ⟨hs₂, he₂⟩ := h₂
  have hx₁ : u π₁ ∈ Ici m := hm _ hs₁
  have hx₂ : u π₂ ∈ Ici m := hm _ hs₂
  have hn := hσLip _ hx₁ _ hx₂
  rw [← he₁, ← he₂] at hn
  have hl := hL _ hs₁ _ hs₂
  have hN0 : 0 ≤ ∑ a, |π₁ a - π₂ a| := sum_nonneg fun a _ => abs_nonneg _
  have hCP : C * (2 * ((m + dmin) * (m + dmax))) = β * (dmax - dmin) := by
    have : m + dmin ≠ 0 := by linarith
    have : m + dmax ≠ 0 := by linarith
    rw [hC]
    field_simp
  have hLC : L * C < 1 := by
    have : L * C * (2 * ((m + dmin) * (m + dmax))) < 1 * (2 * ((m + dmin) * (m + dmax))) := by
      rw [mul_assoc, hCP]
      nlinarith [hsmall]
    exact lt_of_mul_lt_mul_right this (by positivity)
  have hδ : |u π₁ - u π₂| = 0 := by
    rcases le_or_gt 0 L with hL0 | hL0
    · have := mul_le_mul_of_nonneg_left hn hL0
      nlinarith [abs_nonneg (u π₁ - u π₂)]
    · nlinarith [abs_nonneg (u π₁ - u π₂)]
  have heq : u π₁ = u π₂ := by
    rw [abs_eq_zero] at hδ
    linarith
  calc π₁ = powerLawPolicy β d (u π₁) := he₁
  _ = powerLawPolicy β d (u π₂) := by rw [heq]
  _ = π₂ := he₂.symm

end EmpoHomotopy
