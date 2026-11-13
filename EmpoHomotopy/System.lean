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
evaluation operator `Φ`, aggregation `Ψ`, and the real parameters `β`, `γ_r`. -/
structure SysData (S A H G : Type*) [Fintype S] where
  /-- robot transition kernel `K(s,a,s')` (human and goal expectations folded in) -/
  K : S → A → S → ℝ
  /-- human evaluation operator: solutions satisfy `Ve = Φ π Ve` -/
  Φ : (S → A → ℝ) → (H → G → S → ℝ) → (H → G → S → ℝ)
  /-- aggregation: `U(s) = Ψ s (Ve(·,·,s))` -/
  Ψ : S → (H → G → ℝ) → ℝ
  β : ℝ
  γr : ℝ
  K_nonneg : ∀ s a s', 0 ≤ K s a s'
  K_sum_le : ∀ s a, ∑ s', K s a s' ≤ 1

variable {S A H G : Type*} [Fintype S] [Fintype A]

namespace SysData

variable (D : SysData S A H G)

/-- `U(s) := Ψ s (Ve(·,·,s))`. -/
def U (Ve : H → G → S → ℝ) (s : S) : ℝ := D.Ψ s fun h g => Ve h g s

/-- **Solution** of the abstract system (STATEMENTS.md §0): for all `s, a`,
`π(s) ∈ Δ(A)`, `Q(s,a) < 0`, `π(s)(a) = (−Q(s,a))^(−β) / ∑_b (−Q(s,b))^(−β)`, `Ve = Φ π Ve`,
`U(s) < 0`, `Vr(s) = U(s) + ∑_a π(s)(a) Q(s,a)`, `Q(s,a) = γ_r ∑_{s'} K(s,a,s') Vr(s')`. -/
structure IsSolution (π Q : S → A → ℝ) (Ve : H → G → S → ℝ) (Vr : S → ℝ) : Prop where
  pi_nonneg : ∀ s a, 0 ≤ π s a
  pi_sum : ∀ s, ∑ a, π s a = 1
  Q_neg : ∀ s a, Q s a < 0
  pi_eq : ∀ s a, π s a = (-Q s a) ^ (-D.β) / ∑ b, (-Q s b) ^ (-D.β)
  Ve_eq : Ve = D.Φ π Ve
  U_neg : ∀ s, D.U Ve s < 0
  Vr_eq : ∀ s, Vr s = D.U Ve s + ∑ a, π s a * Q s a
  Q_eq : ∀ s a, Q s a = D.γr * ∑ s', D.K s a s' * Vr s'

/-- **UniqEval**: for every policy `π` with `π(s) ∈ Δ(A)` for all `s`, there is at most one
`Ve` with `Ve = Φ π Ve`. -/
def UniqEval : Prop :=
  ∀ π : S → A → ℝ, (∀ s a, 0 ≤ π s a) → (∀ s, ∑ a, π s a = 1) →
    ∀ V W : H → G → S → ℝ, V = D.Φ π V → W = D.Φ π W → V = W

/-- **Locality** of `Φ` w.r.t. a rank `ρ`: `(Φ π v)(h,g,s)` depends on `π` only through `π(s)`
and on `v` only through the values `v(h',g',s')` with `ρ(s') < ρ(s)`. -/
def LocalEval (ρ : S → ℕ) : Prop :=
  ∀ (π π' : S → A → ℝ) (v v' : H → G → S → ℝ) (h : H) (g : G) (s : S), π s = π' s →
    (∀ h' g' s', ρ s' < ρ s → v h' g' s' = v' h' g' s') → D.Φ π v h g s = D.Φ π' v' h g s

end SysData

omit [Fintype S] in
/-- `∑_a π_a q_a = −w_β(−q)` for `π ∝ (−q)^(−β)`, `q < 0`. -/
lemma sum_pi_mul_Q {β : ℝ} {π Q : S → A → ℝ} (hQ : ∀ s a, Q s a < 0)
    (hπ : ∀ s a, π s a = (-Q s a) ^ (-β) / ∑ b, (-Q s b) ^ (-β)) (s : S) :
    ∑ a, π s a * Q s a = -lehmer β (fun a => -Q s a) := by
  have h : ∀ a, π s a * Q s a = -((-Q s a) ^ (1 - β)) / ∑ b, (-Q s b) ^ (-β) := by
    intro a
    rw [hπ, rpow_one_sub_eq (neg_pos.2 (hQ s a))]
    ring
  rw [Finset.sum_congr rfl fun a _ => h a, ← Finset.sum_div, Finset.sum_neg_distrib, lehmer,
    neg_div]

namespace SysData

variable {D : SysData S A H G} {π Q : S → A → ℝ} {Ve : H → G → S → ℝ} {Vr : S → ℝ}

/-- With `x = −Q`, `c = −U`: `x(s,a) = γ_r ∑_{s'} K(s,a,s') (c(s') + w_β(x(s',·)))`. -/
lemma IsSolution.bellman (hs : D.IsSolution π Q Ve Vr) (s : S) (a : A) :
    -Q s a = D.γr * ∑ s', D.K s a s' * (-D.U Ve s' + lehmer D.β (fun b => -Q s' b)) := by
  have hV : ∀ s', Vr s' = -(-D.U Ve s' + lehmer D.β (fun b => -Q s' b)) := by
    intro s'
    rw [hs.Vr_eq, sum_pi_mul_Q hs.Q_neg hs.pi_eq]
    ring
  rw [hs.Q_eq]
  simp only [hV, mul_neg, Finset.sum_neg_distrib, neg_neg]

/-- Robot side of SYS-1: same `U` and `β ∈ [0,1]` give the same `Q`. -/
lemma sys1_Q [Nonempty A] (hβ0 : 0 ≤ D.β) (hβ1 : D.β ≤ 1)
    {π₁ Q₁ π₂ Q₂ : S → A → ℝ} {Ve₁ Ve₂ : H → G → S → ℝ} {Vr₁ Vr₂ : S → ℝ}
    (h₁ : D.IsSolution π₁ Q₁ Ve₁ Vr₁) (h₂ : D.IsSolution π₂ Q₂ Ve₂ Vr₂)
    (hU : D.U Ve₁ = D.U Ve₂) : Q₁ = Q₂ := by
  rcases isEmpty_or_nonempty S with hS | ⟨⟨s₀⟩⟩
  · funext s; exact (IsEmpty.false s).elim
  obtain ⟨a₀⟩ := ‹Nonempty A›
  have hc : ∀ s, 0 < -D.U Ve₁ s := fun s => neg_pos.2 (h₁.U_neg s)
  have e₁ := h₁.bellman
  have e₂ := h₂.bellman
  rw [← hU] at e₂
  have hw : ∀ s', 0 ≤ lehmer D.β (fun b => -Q₁ s' b) := fun s' =>
    le_lehmer_of_le D.β (fun b => neg_pos.2 (h₁.Q_neg s' b)) fun b => (neg_pos.2 (h₁.Q_neg s' b)).le
  have hT : ∀ s a, 0 ≤ ∑ s', D.K s a s' * (-D.U Ve₁ s' + lehmer D.β (fun b => -Q₁ s' b)) :=
    fun s a => Finset.sum_nonneg fun s' _ =>
      mul_nonneg (D.K_nonneg s a s') (add_pos_of_pos_of_nonneg (hc s') (hw s')).le
  have hγ : 0 < D.γr := by
    by_contra hne
    replace hne : D.γr ≤ 0 := not_lt.mp hne
    have h1 := e₁ s₀ a₀
    have h2 := h₁.Q_neg s₀ a₀
    have h3 := mul_nonpos_of_nonpos_of_nonneg hne (hT s₀ a₀)
    linarith
  -- the constant term `c'(s,a) = γ_r ∑ K(s,a,s') c(s')` is positive
  set c' : S × A → ℝ := fun p => D.γr * ∑ s', D.K p.1 p.2 s' * (-D.U Ve₁ s') with hc'_def
  have hc' : ∀ p, 0 < c' p := by
    rintro ⟨s, a⟩
    have hne : ∑ s', D.K s a s' * (-D.U Ve₁ s' + lehmer D.β (fun b => -Q₁ s' b)) ≠ 0 := by
      intro h0
      have := e₁ s a
      rw [h0, mul_zero] at this
      linarith [h₁.Q_neg s a]
    obtain ⟨s', -, hs'⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
    have hK : 0 < D.K s a s' :=
      lt_of_le_of_ne (D.K_nonneg s a s') fun h => hs' (by rw [← h, zero_mul])
    exact mul_pos hγ (Finset.sum_pos' (fun i _ => mul_nonneg (D.K_nonneg s a i) (hc i).le)
      ⟨s', mem_univ _, mul_pos hK (hc s')⟩)
  obtain ⟨hmono, hhom, -⟩ := lehmerBellmanOp_hyps hβ0 hβ1 (T := fun p s' => D.K p.1 p.2 s')
    (fun p s' => D.K_nonneg _ _ _)
  have hfix : ∀ {Q : S → A → ℝ},
      (∀ s a, -Q s a = D.γr * ∑ s', D.K s a s' * (-D.U Ve₁ s' + lehmer D.β (fun b => -Q s' b))) →
      (fun p : S × A => -Q p.1 p.2) =
        c' + D.γr • lehmerBellmanOp D.β (fun p s' => D.K p.1 p.2 s') (fun p => -Q p.1 p.2) := by
    intro Q e
    funext p
    simp only [hc'_def, Pi.add_apply, Pi.smul_apply, smul_eq_mul, lehmerBellmanOp]
    rw [e, ← mul_add, ← Finset.sum_add_distrib]
    congr 1
    exact Finset.sum_congr rfl fun s' _ => by ring
  have key := bel1 hc' hγ.le hmono hhom (x := fun p => -Q₁ p.1 p.2) (y := fun p => -Q₂ p.1 p.2)
    (fun p => neg_pos.2 (h₁.Q_neg p.1 p.2)) (fun p => neg_pos.2 (h₂.Q_neg p.1 p.2))
    (hfix e₁) (hfix e₂)
  funext s a
  have := congrFun key (s, a)
  simp only [neg_inj] at this
  exact this

/-- SYS-1 core with the conclusion on `π` and `Vr`. -/
lemma sys1_robot [Nonempty A] (hβ0 : 0 ≤ D.β) (hβ1 : D.β ≤ 1)
    {π₁ Q₁ π₂ Q₂ : S → A → ℝ} {Ve₁ Ve₂ : H → G → S → ℝ} {Vr₁ Vr₂ : S → ℝ}
    (h₁ : D.IsSolution π₁ Q₁ Ve₁ Vr₁) (h₂ : D.IsSolution π₂ Q₂ Ve₂ Vr₂)
    (hU : D.U Ve₁ = D.U Ve₂) : Q₁ = Q₂ ∧ π₁ = π₂ ∧ Vr₁ = Vr₂ := by
  have hQ : Q₁ = Q₂ := sys1_Q hβ0 hβ1 h₁ h₂ hU
  have hπ : π₁ = π₂ := by
    funext s a
    rw [h₁.pi_eq, h₂.pi_eq, hQ]
  refine ⟨hQ, hπ, ?_⟩
  funext s
  rw [h₁.Vr_eq, h₂.Vr_eq, hU, hπ, hQ]

end SysData

open SysData

/-- **SYS-1 (robot side determined by `U` for `β ≤ 1`).**  Let `A` be nonempty and `β ∈ [0,1]`.
If `(π₁,Q₁,Ve₁,Vr₁)` and `(π₂,Q₂,Ve₂,Vr₂)` are solutions of the abstract system with the same
`U` (i.e. `Ψ s (Ve₁(·,·,s)) = Ψ s (Ve₂(·,·,s))` for all `s`), then `Q₁ = Q₂`, `π₁ = π₂`,
`Vr₁ = Vr₂`; if moreover `Φ` has UniqEval, then also `Ve₁ = Ve₂`.
No sign or size condition on `γ_r` is needed (`Q < 0` forces `γ_r > 0` when `S` is nonempty). -/
theorem sys1 [Nonempty A] (D : SysData S A H G) (hβ0 : 0 ≤ D.β) (hβ1 : D.β ≤ 1)
    {π₁ Q₁ π₂ Q₂ : S → A → ℝ} {Ve₁ Ve₂ : H → G → S → ℝ} {Vr₁ Vr₂ : S → ℝ}
    (h₁ : D.IsSolution π₁ Q₁ Ve₁ Vr₁) (h₂ : D.IsSolution π₂ Q₂ Ve₂ Vr₂)
    (hU : D.U Ve₁ = D.U Ve₂) :
    Q₁ = Q₂ ∧ π₁ = π₂ ∧ Vr₁ = Vr₂ ∧ (D.UniqEval → Ve₁ = Ve₂) := by
  obtain ⟨hQ, hπ, hVr⟩ := sys1_robot hβ0 hβ1 h₁ h₂ hU
  refine ⟨hQ, hπ, hVr, fun hE => ?_⟩
  have h₂' := h₂.Ve_eq
  rw [← hπ] at h₂'
  exact hE π₁ h₁.pi_nonneg h₁.pi_sum Ve₁ Ve₂ h₁.Ve_eq h₂'

/-- **SYS-2 (`β = 0`).**  Let `A` be nonempty, `β = 0`, and let `Φ` have UniqEval.  Then the
abstract system has at most one solution `(π, Q, Ve, Vr)`.
(No hypothesis on `γ_r` is needed; STATEMENTS.md assumes `γ_r ∈ [0,1)`.) -/
theorem sys2 [Nonempty A] (D : SysData S A H G) (hβ : D.β = 0) (hE : D.UniqEval)
    {π₁ Q₁ π₂ Q₂ : S → A → ℝ} {Ve₁ Ve₂ : H → G → S → ℝ} {Vr₁ Vr₂ : S → ℝ}
    (h₁ : D.IsSolution π₁ Q₁ Ve₁ Vr₁) (h₂ : D.IsSolution π₂ Q₂ Ve₂ Vr₂) :
    π₁ = π₂ ∧ Q₁ = Q₂ ∧ Ve₁ = Ve₂ ∧ Vr₁ = Vr₂ := by
  have hπ : π₁ = π₂ := by
    funext s a
    rw [h₁.pi_eq, h₂.pi_eq, hβ]
    simp
  have h₂' := h₂.Ve_eq
  rw [← hπ] at h₂'
  have hVe : Ve₁ = Ve₂ := hE π₁ h₁.pi_nonneg h₁.pi_sum Ve₁ Ve₂ h₁.Ve_eq h₂'
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
      rw [h₁.pi_eq s a, h₂.pi_eq s a]
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
one `v` with `v = linearΦ r γ_h Kh π v` (any real `r`). -/
theorem sys_linear_uniqEval (D : SysData S A H G) {r : H → G → S → A → ℝ} {γh : ℝ}
    {Kh : H → G → S → A → S → ℝ} (hΦ : D.Φ = linearΦ r γh Kh) (hγ0 : 0 ≤ γh) (hγ1 : γh < 1)
    (hKh0 : ∀ h g s a s', 0 ≤ Kh h g s a s') (hKh1 : ∀ h g s a, ∑ s', Kh h g s a s' ≤ 1) :
    D.UniqEval := by
  intro π hπ0 hπ1 V W hV hW
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

end EmpoHomotopy
