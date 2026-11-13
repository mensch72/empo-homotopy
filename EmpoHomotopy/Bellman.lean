import EmpoHomotopy.Lehmer

/-!
# Robot-side Bellman equation (STATEMENTS.md §3)

`x = c + γ M(x)` on `(0,∞)^Ω`, with `M` monotone and positively homogeneous of degree 1
on pointwise-positive vectors.
-/

open Finset

noncomputable section

namespace EmpoHomotopy

variable {Ω : Type*} [Fintype Ω]

/-- One half of BEL-1: any two positive solutions satisfy `x ≤ y` pointwise. -/
lemma bellman_le {c : Ω → ℝ} (hc : ∀ ω, 0 < c ω) {γ : ℝ} (hγ : 0 ≤ γ)
    {M : (Ω → ℝ) → (Ω → ℝ)}
    (hmono : ∀ x y : Ω → ℝ, (∀ ω, 0 < x ω) → (∀ ω, x ω ≤ y ω) → ∀ ω, M x ω ≤ M y ω)
    (hhom : ∀ l : ℝ, 0 < l → ∀ x : Ω → ℝ, (∀ ω, 0 < x ω) → M (l • x) = l • M x)
    {x y : Ω → ℝ} (hx : ∀ ω, 0 < x ω) (hy : ∀ ω, 0 < y ω)
    (hxe : x = c + γ • M x) (hye : y = c + γ • M y) : ∀ ω, x ω ≤ y ω := by
  by_cases hΩ : Nonempty Ω
  swap
  · exact fun ω => (hΩ ⟨ω⟩).elim
  set r : Ω → ℝ := fun ω => x ω / y ω
  set l := univ.sup' univ_nonempty r with hl_def
  have hrl : ∀ ω, r ω ≤ l := fun ω => le_sup' r (mem_univ ω)
  obtain ⟨ω₀, -, hω₀⟩ := exists_mem_eq_sup' (univ_nonempty (α := Ω)) r
  suffices hl1 : l ≤ 1 by
    intro ω
    have := (hrl ω).trans hl1
    rwa [div_le_one (hy ω)] at this
  by_contra hl1
  replace hl1 : 1 < l := not_le.mp hl1
  have hl0 : 0 < l := by linarith
  have hxly : ∀ ω, x ω ≤ (l • y) ω := fun ω => by
    have := hrl ω
    rw [div_le_iff₀ (hy ω)] at this
    simpa [Pi.smul_apply, smul_eq_mul, mul_comm] using this
  have hM := hmono x (l • y) hx hxly
  rw [hhom l hl0 y hy] at hM
  -- `x < l y` pointwise
  have hlt : ∀ ω, x ω < l * y ω := by
    intro ω
    have h1 : x ω = c ω + γ * M x ω := by
      conv_lhs => rw [hxe]
      simp
    have h2 : y ω = c ω + γ * M y ω := by
      conv_lhs => rw [hye]
      simp
    have h3 : M x ω ≤ l * M y ω := by simpa using hM ω
    have h4 : γ * M x ω ≤ γ * (l * M y ω) := mul_le_mul_of_nonneg_left h3 hγ
    have h5 := hc ω
    nlinarith
  have := hlt ω₀
  have h6 : r ω₀ < l := by
    show x ω₀ / y ω₀ < l
    rw [div_lt_iff₀ (hy ω₀)]
    linarith
  have h7 : l = r ω₀ := hω₀
  linarith

/-- **BEL-1 (uniqueness).** Let `Ω` be finite, `c ∈ (0,∞)^Ω`, `γ ≥ 0`, and let
`M : (0,∞)^Ω → ℝ^Ω` be monotone (`x ≤ y ⇒ M x ≤ M y`) and positively homogeneous of degree 1
(`M (λ x) = λ M x` for `λ > 0`) on pointwise-positive vectors.  Then the equation
`x = c + γ M(x)` has at most one solution `x ∈ (0,∞)^Ω`. -/
theorem bel1 {c : Ω → ℝ} (hc : ∀ ω, 0 < c ω) {γ : ℝ} (hγ : 0 ≤ γ)
    {M : (Ω → ℝ) → (Ω → ℝ)}
    (hmono : ∀ x y : Ω → ℝ, (∀ ω, 0 < x ω) → (∀ ω, x ω ≤ y ω) → ∀ ω, M x ω ≤ M y ω)
    (hhom : ∀ l : ℝ, 0 < l → ∀ x : Ω → ℝ, (∀ ω, 0 < x ω) → M (l • x) = l • M x)
    {x y : Ω → ℝ} (hx : ∀ ω, 0 < x ω) (hy : ∀ ω, 0 < y ω)
    (hxe : x = c + γ • M x) (hye : y = c + γ • M y) : x = y :=
  funext fun ω => le_antisymm (bellman_le hc hγ hmono hhom hx hy hxe hye ω)
    (bellman_le hc hγ hmono hhom hy hx hye hxe ω)

/-- **BEL-2 (existence).** Let `Ω` be finite, `c ∈ (0,∞)^Ω`, `0 ≤ γ < 1`, and let
`M : (0,∞)^Ω → [0,∞)^Ω` be monotone, continuous on `(0,∞)^Ω`, and satisfy `M(x) ≤ max x`
pointwise (stated as: `x ≤ b` pointwise implies `M x ≤ b` pointwise).  Then `x = c + γ M(x)`
has a solution `x ∈ (0,∞)^Ω`, namely the limit of the monotone iteration from `x⁰ = c`. -/
theorem bel2 {c : Ω → ℝ} (hc : ∀ ω, 0 < c ω) {γ : ℝ} (hγ0 : 0 ≤ γ) (hγ1 : γ < 1)
    {M : (Ω → ℝ) → (Ω → ℝ)}
    (hmono : ∀ x y : Ω → ℝ, (∀ ω, 0 < x ω) → (∀ ω, x ω ≤ y ω) → ∀ ω, M x ω ≤ M y ω)
    (hnonneg : ∀ x : Ω → ℝ, (∀ ω, 0 < x ω) → ∀ ω, 0 ≤ M x ω)
    (hmax : ∀ x : Ω → ℝ, (∀ ω, 0 < x ω) → ∀ b : ℝ, (∀ ω, x ω ≤ b) → ∀ ω, M x ω ≤ b)
    (hcont : ContinuousOn M {x | ∀ ω, 0 < x ω}) :
    ∃ x : Ω → ℝ, (∀ ω, 0 < x ω) ∧ x = c + γ • M x := by
  let F : (Ω → ℝ) → (Ω → ℝ) := fun x => c + γ • M x
  let X : ℕ → Ω → ℝ := fun k => F^[k] c
  have hXs : ∀ k, X (k + 1) = F (X k) := fun k => Function.iterate_succ_apply' F k c
  have hXs' : ∀ k ω, X (k + 1) ω = c ω + γ * M (X k) ω := fun k ω => by
    rw [hXs]; rfl
  have hge : ∀ k ω, c ω ≤ X k ω := by
    intro k
    induction k with
    | zero => intro ω; exact le_rfl
    | succ k ih =>
      intro ω
      rw [hXs']
      have := hnonneg (X k) (fun ω => (hc ω).trans_le (ih ω)) ω
      nlinarith
  have hXpos : ∀ k ω, 0 < X k ω := fun k ω => (hc ω).trans_le (hge k ω)
  have hmon : ∀ k ω, X k ω ≤ X (k + 1) ω := by
    intro k
    induction k with
    | zero => intro ω; exact hge 1 ω
    | succ k ih =>
      intro ω
      rw [hXs' (k + 1), hXs' k]
      have := hmono _ _ (hXpos k) ih ω
      nlinarith
  set b := (∑ ω, c ω) / (1 - γ) with hb_def
  have hcb : ∀ ω, c ω ≤ (1 - γ) * b := fun ω => by
    rw [hb_def, mul_div_cancel₀ _ (by linarith : (1 - γ) ≠ 0)]
    exact single_le_sum (fun i _ => (hc i).le) (mem_univ ω)
  have hb : ∀ k ω, X k ω ≤ b := by
    intro k
    induction k with
    | zero => intro ω; show c ω ≤ b; nlinarith [hcb ω, hc ω]
    | succ k ih =>
      intro ω
      rw [hXs']
      have := hmax _ (hXpos k) b ih ω
      nlinarith [hcb ω]
  have hmonoω : ∀ ω, Monotone fun k => X k ω := fun ω =>
    monotone_nat_of_le_succ fun k => hmon k ω
  have hbdd : ∀ ω, BddAbove (Set.range fun k => X k ω) := fun ω =>
    ⟨b, by rintro _ ⟨k, rfl⟩; exact hb k ω⟩
  set xs : Ω → ℝ := fun ω => ⨆ k, X k ω
  have hlim : Filter.Tendsto X Filter.atTop (nhds xs) :=
    tendsto_pi_nhds.2 fun ω => tendsto_atTop_ciSup (hmonoω ω) (hbdd ω)
  have hxspos : ∀ ω, 0 < xs ω := fun ω => (hXpos 0 ω).trans_le (le_ciSup (hbdd ω) 0)
  have hMlim : Filter.Tendsto (fun k => M (X k)) Filter.atTop (nhds (M xs)) :=
    (hcont xs hxspos).tendsto.comp
      (tendsto_nhdsWithin_iff.2 ⟨hlim, Filter.Eventually.of_forall fun k => hXpos k⟩)
  have hlim2 : Filter.Tendsto (fun k => X (k + 1)) Filter.atTop (nhds (F xs)) := by
    simp_rw [hXs]
    exact tendsto_const_nhds.add (hMlim.const_smul γ)
  have hlim1 : Filter.Tendsto (fun k => X (k + 1)) Filter.atTop (nhds xs) :=
    hlim.comp (Filter.tendsto_add_atTop_nat 1)
  exact ⟨xs, hxspos, tendsto_nhds_unique hlim1 hlim2⟩

/-- The Lehmer-based robot Bellman operator on `Ω = S × A`:
`M(x)(s,a) = ∑_{s'} T(s,a)(s') · w_β(x(s',·))`. -/
def lehmerBellmanOp {S A : Type*} [Fintype S] [Fintype A] (β : ℝ) (T : S × A → S → ℝ)
    (x : S × A → ℝ) : S × A → ℝ :=
  fun p => ∑ s', T p s' * lehmer β (fun a => x (s', a))

/-- Instance lemma for BEL-1 (STATEMENTS.md §3): for `β ∈ [0,1]` and a nonnegative kernel `T`
(in particular a row-stochastic one), the Lehmer-based operator is monotone, positively
homogeneous of degree 1 and nonnegative on pointwise-positive vectors. -/
theorem lehmerBellmanOp_hyps {S A : Type*} [Fintype S] [Fintype A] [Nonempty A] {β : ℝ}
    (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1) {T : S × A → S → ℝ} (hT : ∀ p s', 0 ≤ T p s') :
    (∀ x y : S × A → ℝ, (∀ ω, 0 < x ω) → (∀ ω, x ω ≤ y ω) →
        ∀ ω, lehmerBellmanOp β T x ω ≤ lehmerBellmanOp β T y ω) ∧
      (∀ l : ℝ, 0 < l → ∀ x : S × A → ℝ, (∀ ω, 0 < x ω) →
        lehmerBellmanOp β T (l • x) = l • lehmerBellmanOp β T x) ∧
      (∀ x : S × A → ℝ, (∀ ω, 0 < x ω) → ∀ ω, 0 ≤ lehmerBellmanOp β T x ω) := by
  refine ⟨fun x y hx hxy p => ?_, fun l hl x hx => ?_, fun x hx p => ?_⟩
  · refine Finset.sum_le_sum fun s' _ => mul_le_mul_of_nonneg_left ?_ (hT p s')
    exact leh2 hβ0 hβ1 (fun a => hx (s', a)) fun a => hxy (s', a)
  · funext p
    simp only [lehmerBellmanOp, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun s' _ => ?_
    rw [(leh1 β _ fun a => hx (s', a)).2.2 l hl]
    ring
  · refine Finset.sum_nonneg fun s' _ => mul_nonneg (hT p s') ?_
    exact le_lehmer_of_le β (fun a => hx (s', a)) fun a => (hx (s', a)).le

end EmpoHomotopy
