import Mathlib

/-!
# Lehmer mean (STATEMENTS.md §2)

For `x : A → ℝ` with positive entries, `lehmer β x = (∑ a, x a ^ (1-β)) / ∑ a, x a ^ (-β)`.
-/

open Finset

noncomputable section

namespace EmpoHomotopy

variable {A : Type*} [Fintype A]

/-- The Lehmer-type mean `w_β(x) = ∑ₐ xₐ^(1-β) / ∑ₐ xₐ^(-β)`. -/
def lehmer (β : ℝ) (x : A → ℝ) : ℝ :=
  (∑ a, x a ^ (1 - β)) / ∑ a, x a ^ (-β)

lemma rpow_one_sub_eq {t : ℝ} (ht : 0 < t) (β : ℝ) : t ^ (1 - β) = t * t ^ (-β) := by
  rw [sub_eq_add_neg, Real.rpow_add ht, Real.rpow_one]

variable [Nonempty A]

lemma lehmer_denom_pos (β : ℝ) {x : A → ℝ} (hx : ∀ a, 0 < x a) : 0 < ∑ a, x a ^ (-β) :=
  Finset.sum_pos (fun a _ => Real.rpow_pos_of_pos (hx a) _) univ_nonempty

lemma le_lehmer_of_le (β : ℝ) {x : A → ℝ} (hx : ∀ a, 0 < x a) {lo : ℝ} (hlo : ∀ a, lo ≤ x a) :
    lo ≤ lehmer β x := by
  unfold lehmer
  rw [le_div_iff₀ (lehmer_denom_pos β hx), Finset.mul_sum]
  refine Finset.sum_le_sum fun a _ => ?_
  rw [rpow_one_sub_eq (hx a)]
  exact mul_le_mul_of_nonneg_right (hlo a) (Real.rpow_pos_of_pos (hx a) _).le

lemma lehmer_le_of_le (β : ℝ) {x : A → ℝ} (hx : ∀ a, 0 < x a) {hi : ℝ} (hhi : ∀ a, x a ≤ hi) :
    lehmer β x ≤ hi := by
  unfold lehmer
  rw [div_le_iff₀ (lehmer_denom_pos β hx), Finset.mul_sum]
  refine Finset.sum_le_sum fun a _ => ?_
  rw [rpow_one_sub_eq (hx a)]
  exact mul_le_mul_of_nonneg_right (hhi a) (Real.rpow_pos_of_pos (hx a) _).le

/-- **LEH-1.** For every real `β` and every `x ∈ (0,∞)^A` (`A` finite, nonempty):
`min x ≤ w_β(x) ≤ max x`, and `w_β(λ x) = λ w_β(x)` for every `λ > 0`. -/
theorem leh1 (β : ℝ) (x : A → ℝ) (hx : ∀ a, 0 < x a) :
    univ.inf' univ_nonempty x ≤ lehmer β x ∧ lehmer β x ≤ univ.sup' univ_nonempty x ∧
      ∀ l : ℝ, 0 < l → lehmer β (fun a => l * x a) = l * lehmer β x := by
  refine ⟨le_lehmer_of_le β hx fun a => inf'_le _ (mem_univ a),
    lehmer_le_of_le β hx fun a => le_sup' _ (mem_univ a), fun l hl => ?_⟩
  have hD := lehmer_denom_pos β hx
  unfold lehmer
  simp_rw [Real.mul_rpow hl.le (hx _).le, rpow_one_sub_eq hl, ← Finset.mul_sum]
  have : 0 < l ^ (-β) := Real.rpow_pos_of_pos hl _
  field_simp

/-- **LEH-2.** For `β ∈ [0,1]` the mean `w_β` is monotone on `(0,∞)^A`:
if `0 < xₐ ≤ yₐ` for all `a` then `w_β(x) ≤ w_β(y)`. -/
theorem leh2 {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1) {x y : A → ℝ} (hx : ∀ a, 0 < x a)
    (hxy : ∀ a, x a ≤ y a) : lehmer β x ≤ lehmer β y := by
  have hy : ∀ a, 0 < y a := fun a => (hx a).trans_le (hxy a)
  set t := lehmer β x with ht_def
  have ht0 : 0 ≤ t := le_lehmer_of_le β hx fun a => (hx a).le
  -- `g(z) = z^(1-β) - t z^(-β)` is nondecreasing on `(0,∞)`, and `∑ g(xₐ) = 0`.
  have hg : ∀ a, x a ^ (1 - β) - t * x a ^ (-β) ≤ y a ^ (1 - β) - t * y a ^ (-β) := by
    intro a
    have h1 : x a ^ (1 - β) ≤ y a ^ (1 - β) :=
      Real.rpow_le_rpow (hx a).le (hxy a) (by linarith)
    have h2 : y a ^ (-β) ≤ x a ^ (-β) :=
      Real.rpow_le_rpow_of_nonpos (hx a) (hxy a) (by linarith)
    nlinarith
  have hsum := Finset.sum_le_sum fun a (_ : a ∈ univ) => hg a
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum] at hsum
  have hx0 : (∑ a, x a ^ (1 - β)) - t * ∑ a, x a ^ (-β) = 0 := by
    rw [ht_def, lehmer, div_mul_cancel₀ _ (lehmer_denom_pos β hx).ne', sub_self]
  rw [hx0] at hsum
  unfold lehmer
  rw [le_div_iff₀ (lehmer_denom_pos β hy)]
  linarith

/-- **LEH-3.** For `β = 2` and `|A| = 2`, `w_β` is not monotone:
`w(3,1) = 6/5 > 110/101 = w(10,1)` although `(3,1) ≤ (10,1)`. -/
theorem leh3 :
    lehmer 2 ![(3 : ℝ), 1] = 6 / 5 ∧ lehmer 2 ![(10 : ℝ), 1] = 110 / 101 ∧
      (∀ a, ![(3 : ℝ), 1] a ≤ ![(10 : ℝ), 1] a) ∧
      lehmer 2 ![(10 : ℝ), 1] < lehmer 2 ![(3 : ℝ), 1] ∧
      ¬ ∀ x y : Fin 2 → ℝ, (∀ a, 0 < x a) → (∀ a, x a ≤ y a) → lehmer 2 x ≤ lehmer 2 y := by
  have e1 : ∀ t : ℝ, 0 ≤ t → t ^ (1 - (2 : ℝ)) = t⁻¹ := fun t _ => by
    norm_num [Real.rpow_neg_one]
  have e2 : ∀ t : ℝ, 0 ≤ t → t ^ (-(2 : ℝ)) = (t ^ 2)⁻¹ := fun t ht => by
    rw [Real.rpow_neg ht]; norm_cast
  have h3 : lehmer 2 ![(3 : ℝ), 1] = 6 / 5 := by
    simp only [lehmer, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [e1 3 (by norm_num), e1 1 (by norm_num), e2 3 (by norm_num), e2 1 (by norm_num)]
    norm_num
  have h10 : lehmer 2 ![(10 : ℝ), 1] = 110 / 101 := by
    simp only [lehmer, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [e1 10 (by norm_num), e1 1 (by norm_num), e2 10 (by norm_num), e2 1 (by norm_num)]
    norm_num
  have hle : ∀ a, ![(3 : ℝ), 1] a ≤ ![(10 : ℝ), 1] a := by
    intro a; fin_cases a <;> norm_num
  have hlt : lehmer 2 ![(10 : ℝ), 1] < lehmer 2 ![(3 : ℝ), 1] := by
    rw [h3, h10]; norm_num
  refine ⟨h3, h10, hle, hlt, fun H => ?_⟩
  have := H _ _ (by intro a; fin_cases a <;> norm_num) hle
  linarith

end EmpoHomotopy
