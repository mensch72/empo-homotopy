import EmpoHomotopy.System

/-!
# SYS-6: non-uniqueness in a cyclic game (STATEMENTS.md §0)

Two states, three robot actions, one human, one goal.  State `0`: every action returns to `0`;
state `1`: actions `0, 1` go to `0`, action `2` stays in `1` (all deterministic).  Linear `Φ` with
`γ_h = 2/3`, `Kh = K`, reward `1/20` on entering `0` and `1` on entering `1`; `Ψ = paperΨ 2 1 3`
(so `U = −Ve^(−6)`); `β = 2`, `γ_r = 4/5`, admissible set `univ`.

With `p = π(1)(2)`, `w = (3−2p)/(3+17p)`, `c = (20/3)^6` and `m = (w^6 + 4(1−p))/(5−4p)`, a
solution is
`π(0) = (1/3,1/3,1/3)`, `π(1) = ((1−p)/2, (1−p)/2, p)`, `Ve = (3/20, 3/(20w))`,
`Vr = (−5c, −5cm)`, `Q(s,a) = (4/5) Vr(next(s,a))`,
provided `2pm² = 1−p`, i.e. `G(p) = 0` for the polynomial `G` below
(`numerics/cyclic/two_state_exact.py`).  `G` changes sign on `[1/2, 3/5]`, `[19/20, 99/100]` and
`[1 − 10⁻¹⁵, 1 − 10⁻¹⁶]`; the intermediate value theorem gives three distinct solutions.
-/

open Finset

noncomputable section

namespace EmpoHomotopy

namespace NonUnique

/-- Successor: `(1,2) ↦ 1`, every other state–action pair `↦ 0`. -/
def next (s : Fin 2) (a : Fin 3) : Fin 2 := if s = 1 ∧ a = 2 then 1 else 0

/-- Deterministic kernel `K(s,a,s') = 1` iff `s' = next(s,a)`. -/
def K (s : Fin 2) (a : Fin 3) (s' : Fin 2) : ℝ := if s' = next s a then 1 else 0

/-- Reward `r(s,a) = 1/20` if the successor is `0`, `1` if the successor is `1`. -/
def r (s : Fin 2) (a : Fin 3) : ℝ := if next s a = 1 then 1 else 1 / 20

/-- The SYS-6 instance. -/
def D : SysData (Fin 2) (Fin 3) Unit Unit where
  K := K
  Φ := linearΦ (fun _ _ => r) (2 / 3) (fun _ _ => K)
  Ψ := paperΨ 2 1 3
  β := 2
  γr := 4 / 5
  adm := Set.univ
  K_nonneg := by intro s a s'; unfold K; split_ifs <;> norm_num
  K_sum_le := by intro s a; fin_cases s <;> fin_cases a <;> norm_num [Fin.sum_univ_two, K, next]

/-- The scalar reduction, denominators cleared: zeros in `(0,1)` ↔ solutions. -/
def G (p : ℝ) : ℝ :=
  2 * p * ((3 - 2 * p) ^ 6 + 4 * (1 - p) * (3 + 17 * p) ^ 6) ^ 2 -
    (1 - p) * (5 - 4 * p) ^ 2 * (3 + 17 * p) ^ 12

def w (p : ℝ) : ℝ := (3 - 2 * p) / (3 + 17 * p)
def m (p : ℝ) : ℝ := (w p ^ 6 + 4 * (1 - p)) / (5 - 4 * p)
def c : ℝ := (20 / 3) ^ 6

def πp (p : ℝ) (s : Fin 2) (a : Fin 3) : ℝ := if s = 0 then 1 / 3 else if a = 2 then p else (1 - p) / 2
def Vep (p : ℝ) : Unit → Unit → Fin 2 → ℝ := fun _ _ s => if s = 0 then 3 / 20 else 3 / 20 / w p
def Vrp (p : ℝ) (s : Fin 2) : ℝ := if s = 0 then -5 * c else -5 * c * m p
def Qp (p : ℝ) (s : Fin 2) (a : Fin 3) : ℝ := if s = 1 ∧ a = 2 then -4 * c * m p else -4 * c

lemma not_terminal (s : Fin 2) : ¬ D.terminal s := by
  intro h
  have := h 0 0
  fin_cases s <;> simp [D, K, next] at this

lemma U_eq (p : ℝ) (s : Fin 2) : D.U (Vep p) s = -((Vep p () () s ^ 2)⁻¹) ^ 3 := by
  simp [SysData.U, D, paperΨ, Real.rpow_neg_one]

/-- One root of `G` in `(0,1)` gives a solution. -/
theorem isSolution_of_root {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (hG : G p = 0) :
    D.IsSolution (πp p) (Qp p) (Vep p) (Vrp p) := by
  have hc : 0 < c := by unfold c; norm_num
  have hw : 0 < w p := by unfold w; apply div_pos <;> linarith
  have h54 : 0 < 5 - 4 * p := by linarith
  have hm : 0 < m p := by
    unfold m; apply div_pos _ h54; nlinarith [pow_pos hw 6]
  have h3 : 0 < 3 + 17 * p := by linarith
  have h32 : 0 < 3 - 2 * p := by linarith
  -- the root condition
  have hroot : 2 * p * m p ^ 2 = 1 - p := by
    have hmw : m p * (5 - 4 * p) = w p ^ 6 + 4 * (1 - p) := by
      unfold m; field_simp
    have hww : w p * (3 + 17 * p) = 3 - 2 * p := by unfold w; field_simp
    have key : G p = (3 + 17 * p) ^ 12 * (5 - 4 * p) ^ 2 * (2 * p * m p ^ 2 - (1 - p)) := by
      unfold G
      rw [← hww]
      have : m p ^ 2 * (5 - 4 * p) ^ 2 = (w p ^ 6 + 4 * (1 - p)) ^ 2 := by rw [← hmw]; ring
      linear_combination (-2 * p * (3 + 17 * p) ^ 12) * this
    rw [key] at hG
    have : (3 + 17 * p) ^ 12 * (5 - 4 * p) ^ 2 ≠ 0 := by positivity
    linarith [(mul_eq_zero.mp hG).resolve_left this]
  have hU0 : D.U (Vep p) 0 = -c := by rw [U_eq]; simp [Vep, c]; norm_num
  have hU1 : D.U (Vep p) 1 = -c * w p ^ 6 := by
    rw [U_eq]; simp [Vep, c]; field_simp
  have hβ : -D.β = -(2 : ℝ) := rfl
  constructor
  · intro s _ a
    unfold Qp; split_ifs
    · have := mul_pos hc hm; linarith
    · linarith
  · intro s _ a
    rw [hβ]
    have hx : ∀ x : ℝ, 0 < x → x ^ (-(2 : ℝ)) = (x ^ 2)⁻¹ := by
      intro x hx; rw [Real.rpow_neg hx.le]; norm_num
    rw [Fin.sum_univ_three]
    fin_cases s <;> fin_cases a <;>
      simp [Qp, πp, hx _ (mul_pos (mul_pos (by norm_num : (0:ℝ) < 4) hc) hm),
        hx _ (mul_pos (by norm_num : (0:ℝ) < 4) hc)] <;> field_simp <;>
      linarith [hroot]
  · intro s ht; exact absurd ht (not_terminal s)
  · exact Set.mem_univ _
  · funext h g s
    fin_cases s
    · simp [D, linearΦ, Vep, πp, r, K, next, Fin.sum_univ_two]; norm_num
    · simp [D, linearΦ, Vep, πp, r, K, next, Fin.sum_univ_three, Fin.sum_univ_two]
      unfold w; field_simp; ring
  · intro s
    fin_cases s
    · simp only [Fin.zero_eta, Fin.isValue]; rw [hU0]; linarith
    · simp only [Fin.mk_one, Fin.isValue]; rw [hU1]
      have := mul_pos hc (pow_pos hw 6); linarith
  · intro s
    fin_cases s
    · simp only [Fin.zero_eta, Fin.isValue]; rw [hU0]
      simp [Vrp, Qp, πp]; ring
    · simp only [Fin.mk_one, Fin.isValue]; rw [hU1]
      simp [Vrp, Qp, πp, Fin.sum_univ_three]
      have hmw : m p * (5 - 4 * p) = w p ^ 6 + 4 * (1 - p) := by
        unfold m; field_simp
      linear_combination (-c) * hmw
  · intro s a
    fin_cases s <;> fin_cases a <;>
      simp [D, Qp, Vrp, K, next, Fin.sum_univ_two] <;> ring

lemma G_continuous : Continuous G := by unfold G; fun_prop

lemma exists_root {a b : ℝ} (hab : a ≤ b) (h : G a ≤ 0 ∧ 0 ≤ G b ∨ G b ≤ 0 ∧ 0 ≤ G a) :
    ∃ p ∈ Set.Icc a b, G p = 0 := by
  have h0 : (0 : ℝ) ∈ Set.uIcc (G a) (G b) := Set.mem_uIcc.2 h
  obtain ⟨p, hp, hp0⟩ := intermediate_value_uIcc G_continuous.continuousOn h0
  exact ⟨p, by rwa [Set.uIcc_of_le hab] at hp, hp0⟩

/-- A solution from a root of `G` in `[a,b] ⊆ (0,1)`; `π(1)(2) ∈ [a,b]`. -/
lemma solution_in {a b : ℝ} (ha : 0 < a) (hb : b < 1) (hab : a ≤ b)
    (h : G a ≤ 0 ∧ 0 ≤ G b ∨ G b ≤ 0 ∧ 0 ≤ G a) :
    ∃ π Q Ve Vr, D.IsSolution π Q Ve Vr ∧ π 1 2 ∈ Set.Icc a b := by
  obtain ⟨p, hp, hG⟩ := exists_root hab h
  refine ⟨πp p, Qp p, Vep p, Vrp p,
    isSolution_of_root (by linarith [hp.1]) (by linarith [hp.2]) hG, ?_⟩
  simpa [πp] using hp

end NonUnique

open NonUnique

/-- **SYS-6 (non-uniqueness in a cyclic game).**  Let `S = {0,1}`, `A = {0,1,2}`, one human, one
goal.  Robot kernel (deterministic): from state `0` every action leads to `0`; from state `1`
actions `0, 1` lead to `0` and action `2` leads to `1`.  Linear evaluation
`Ve(s) = ∑_a π(s)(a) [r(s,a) + γ_h Ve(next(s,a))]` with `γ_h = 2/3`, `r(s,a) = 1/20` if the
successor is `0` and `1` if it is `1`; aggregation `U(s) = −((Ve(s)^2)^(−1))^3`
(`paperΨ` with `ζ = 2, ξ = 1, η = 3`); `β = 2`, `γ_r = 4/5`, admissible set `ℝ^S`.
Then the system has two solutions `(π₁,Q₁,Ve₁,Vr₁)`, `(π₂,Q₂,Ve₂,Vr₂)` with `π₁ ≠ π₂`. -/
theorem sys6_two_solutions : ∃ (π₁ Q₁ : Fin 2 → Fin 3 → ℝ) (Ve₁ : Unit → Unit → Fin 2 → ℝ)
    (Vr₁ : Fin 2 → ℝ) (π₂ Q₂ : Fin 2 → Fin 3 → ℝ) (Ve₂ : Unit → Unit → Fin 2 → ℝ)
    (Vr₂ : Fin 2 → ℝ), NonUnique.D.IsSolution π₁ Q₁ Ve₁ Vr₁ ∧
      NonUnique.D.IsSolution π₂ Q₂ Ve₂ Vr₂ ∧ π₁ ≠ π₂ := by
  obtain ⟨π₁, Q₁, Ve₁, Vr₁, h₁, hp₁⟩ :=
    solution_in (a := 1 / 2) (b := 3 / 5) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [G])
  obtain ⟨π₂, Q₂, Ve₂, Vr₂, h₂, hp₂⟩ :=
    solution_in (a := 19 / 20) (b := 99 / 100) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [G])
  refine ⟨π₁, Q₁, Ve₁, Vr₁, π₂, Q₂, Ve₂, Vr₂, h₁, h₂, fun h => ?_⟩
  rw [h] at hp₁
  linarith [hp₁.2, hp₂.1]

end EmpoHomotopy
