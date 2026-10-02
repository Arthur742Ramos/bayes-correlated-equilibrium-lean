module
public import BCE.ScoringGame
public import BCE.ActionReindex
public import BCE.OrderCompactness

@[expose] public section
open scoped BigOperators
namespace BayesCorrelated.OrderImplementation
open BayesCorrelated
universe uI uΘ uT uE
variable {I : Type uI} {Θ : Type uΘ} {T : I → Type uT} {E : I → Type uE}
variable [Fintype I] [DecidableEq I] [Fintype Θ]
variable [∀ i, Fintype (T i)] [∀ i, DecidableEq (T i)]
variable [∀ i, Fintype (E i)] [∀ i, DecidableEq (E i)]

theorem truthful_outcome_at (π : Θ → (∀ i, T i) → ℝ) (θ : Θ) (t : ∀ i, T i) :
    outcome π truthfulRule θ (embedTypes t) = π θ t := by
  classical
  simp [outcome, truthfulRule, embedTypes_injective.eq_iff, mul_ite]

theorem truthful_outcome_off (π : Θ → (∀ i, T i) → ℝ) (θ : Θ)
    (a : ∀ i, TestAction (Θ := Θ) (T := T) i) (h : a ∉ Set.range embedTypes) :
    outcome π truthfulRule θ a = 0 := by
  classical
  have hn (t : ∀ i, T i) : a ≠ embedTypes t := by
    intro ha; exact h ⟨t, ha.symm⟩
  simp [outcome, truthfulRule, hn]

theorem sum_embedTypes (w : (∀ i, TestAction (Θ := Θ) (T := T) i) → ℝ)
    (hw : ∀ a, a ∉ Set.range embedTypes → w a = 0) :
    ∑ t, w (embedTypes t) = ∑ a, w a := by
  classical
  rw [← Finset.sum_image embedTypes_injective.injOn]
  apply Finset.sum_subset (Finset.subset_univ _)
  intro a _ ha
  apply hw a
  rintro ⟨t, rfl⟩
  exact ha (Finset.mem_image.mpr ⟨t, Finset.mem_univ t, rfl⟩)

noncomputable def ruleCombination (ρ : Θ → (∀ i, E i) → ℝ)
    (σ : Θ → (∀ i, E i) → (∀ i, TestAction (Θ := Θ) (T := T) i) → ℝ) :
    Θ → (∀ i, T i) → (∀ i, E i) → ℝ :=
  fun θ t e => ρ θ e * σ θ e (embedTypes t)

theorem transferred_joint_off (π : Θ → (∀ i, T i) → ℝ)
    (ρ : Θ → (∀ i, E i) → ℝ)
    (σ : Θ → (∀ i, E i) → (∀ i, TestAction (Θ := Θ) (T := T) i) → ℝ)
    (hρ : IsInformation ρ) (hσ : IsDecisionRule σ)
    (he : outcome ρ σ = outcome π truthfulRule) (θ : Θ) (e : ∀ i, E i)
    (a : ∀ i, TestAction (Θ := Θ) (T := T) i) (ha : a ∉ Set.range embedTypes) :
    ρ θ e * σ θ e a = 0 := by
  have hz : ∑ e, ρ θ e * σ θ e a = 0 :=
    (congr_fun (congr_fun he θ) a).trans (truthful_outcome_off π θ a ha)
  exact (Finset.sum_eq_zero_iff_of_nonneg
    (fun e _ => mul_nonneg ((hρ θ).1 e) ((hσ θ e).1 a))).mp hz e (Finset.mem_univ e)

theorem ruleCombination_valid (π : Θ → (∀ i, T i) → ℝ)
    (ρ : Θ → (∀ i, E i) → ℝ)
    (σ : Θ → (∀ i, E i) → (∀ i, TestAction (Θ := Θ) (T := T) i) → ℝ)
    (hρ : IsInformation ρ) (hσ : IsDecisionRule σ)
    (he : outcome ρ σ = outcome π truthfulRule) :
    IsCombination π ρ (ruleCombination ρ σ) := by
  constructor
  · constructor
    · intro θ t e; exact mul_nonneg ((hρ θ).1 e) ((hσ θ e).1 _)
    · intro θ t
      exact (congr_fun (congr_fun he θ) (embedTypes t)).trans (truthful_outcome_at π θ t)
  · intro θ e
    change (∑ t, ρ θ e * σ θ e (embedTypes t)) = ρ θ e
    rw [sum_embedTypes (fun a => ρ θ e * σ θ e a)
      (transferred_joint_off π ρ σ hρ hσ he θ e)]
    rw [← Finset.mul_sum, (hσ θ e).2, mul_one]

theorem scoring_game_transfer (ψ : Θ → ℝ) (π : Θ → (∀ i, T i) → ℝ)
    (ρ : Θ → (∀ i, E i) → ℝ) (δ : ℝ)
    (hψ : FullSupportPrior ψ) (hπ : IsInformation π) (hρ : IsInformation ρ)
    (ho : MoreIncentiveConstrained π ρ) :
    ∃ σ : Θ → (∀ i, E i) → (∀ i, TestAction (Θ := Θ) (T := T) i) → ℝ,
      IsDecisionRule σ ∧ BCE ψ ρ (testUtility ψ π δ) σ ∧
      outcome ρ σ = outcome π truthfulRule ∧ IsCombination π ρ (ruleCombination ρ σ) := by
  have hv : IsBCEOutcome ψ π (testUtility ψ π δ) (outcome π truthfulRule) :=
    ⟨truthfulRule, truthfulRule_valid, truthful_BCE ψ π δ hψ.1 hπ, rfl⟩
  obtain ⟨σ, hσ, hb, he⟩ := moreIncentiveConstrained_outcome_any_universe
    ψ π ρ ho hψ (testUtility ψ π δ) (outcome π truthfulRule) hv
  exact ⟨σ, hσ, hb, he, ruleCombination_valid π ρ σ hρ hσ he⟩

noncomputable def coupledScoreMass (ψ : Θ → ℝ)
    (q : Θ → (∀ i, T i) → (∀ i, E i) → ℝ) (i : I) (s : T i) (z : E i)
    (c : ScoreCoordinate (Θ := Θ) (T := T) i) : ℝ :=
  originalMass ψ (fun θ t => ∑ e, if e i = z then q θ t e else 0) i s c

theorem priorMass_eq (ψ : Θ → ℝ) (π : Θ → (∀ i, T i) → ℝ) (i : I) (s : T i) :
    typePriorMass ψ π i s = originalTypeMass ψ π i s := by
  simpa only [typePriorMass, originalTypeMass, mul_one] using
    sum_own_type ψ π i s (fun _ => 1)

theorem coupledMass_eq (ψ : Θ → ℝ)
    (q : Θ → (∀ i, T i) → (∀ i, E i) → ℝ) (i : I) (s : T i) (z : E i) :
    coupledTypeMass ψ q i s z = ∑ c, coupledScoreMass ψ q i s z c := by
  have ht (θ : Θ) (t : ∀ i, T i) :
      (∑ e, if t i = s ∧ e i = z then ψ θ * q θ t e else 0) =
      if t i = s then ψ θ * (∑ e, if e i = z then q θ t e else 0) else 0 := by
    by_cases h : t i = s
    · simp only [h, true_and, ite_true, Finset.mul_sum]
      apply Finset.sum_congr rfl; intro e _; split_ifs <;> simp
    · simp [h]
  unfold coupledTypeMass
  simp_rw [ht]
  simpa only [mul_one, coupledScoreMass] using
    sum_own_type ψ (fun θ t => ∑ e, if e i = z then q θ t e else 0) i s (fun _ => 1)

theorem ruleCombination_scoring_gain (ψ : Θ → ℝ) (π : Θ → (∀ i, T i) → ℝ)
    (ρ : Θ → (∀ i, E i) → ℝ) (δ : ℝ)
    (σ : Θ → (∀ i, E i) → (∀ i, TestAction (Θ := Θ) (T := T) i) → ℝ)
    (hρ : IsInformation ρ) (hσ : IsDecisionRule σ)
    (he : outcome ρ σ = outcome π truthfulRule)
    (i : I) (z : E i) (s : T i) (y : TestAction (Θ := Θ) (T := T) i) :
    obedienceGain ψ ρ (testUtility ψ π δ) σ i z (Sum.inl s) y =
      ∑ c, coupledScoreMass ψ (ruleCombination ρ σ) i s z c *
        (quadraticScore (originalBelief ψ π i s) c - quadraticScore (testReport ψ π δ i y) c) := by
  classical
  unfold obedienceGain
  have ht (θ : Θ) (e : ∀ i, E i) :
      (∑ a, if e i = z ∧ a i = Sum.inl s then ψ θ * ρ θ e * σ θ e a *
        (testUtility ψ π δ i a θ - testUtility ψ π δ i (Function.update a i y) θ) else 0) =
      ∑ t, if e i = z ∧ t i = s then ψ θ * ruleCombination ρ σ θ t e *
        (quadraticScore (originalBelief ψ π i s) (θ, fun j => t j.1) -
          quadraticScore (testReport ψ π δ i y) (θ, fun j => t j.1)) else 0 := by
    rw [← sum_embedTypes (fun a => if e i = z ∧ a i = Sum.inl s then
      ψ θ * ρ θ e * σ θ e a *
        (testUtility ψ π δ i a θ - testUtility ψ π δ i (Function.update a i y) θ) else 0)
      (by intro a ha; split_ifs
          · rw [show ψ θ * ρ θ e * σ θ e a = ψ θ * (ρ θ e * σ θ e a) by ring,
              transferred_joint_off π ρ σ hρ hσ he θ e a ha]; simp
          · rfl)]
    apply Finset.sum_congr rfl; intro t _
    simp only [embedTypes, Sum.inl.injEq]
    rw [testUtility_embed, testUtility_update]
    by_cases h : e i = z ∧ t i = s
    · simp only [h, ite_true, h.2, ruleCombination]; ring
    · simp [h]
  simp_rw [ht]
  conv_lhs => arg 2; ext θ; rw [Finset.sum_comm]
  have hs (θ : Θ) (t : ∀ i, T i) :
      (∑ e, if e i = z ∧ t i = s then ψ θ * ruleCombination ρ σ θ t e *
        (quadraticScore (originalBelief ψ π i s) (θ, fun j => t j.1) -
          quadraticScore (testReport ψ π δ i y) (θ, fun j => t j.1)) else 0) =
      if t i = s then ψ θ * (∑ e, if e i = z then ruleCombination ρ σ θ t e else 0) *
        (quadraticScore (originalBelief ψ π i s) (θ, fun j => t j.1) -
          quadraticScore (testReport ψ π δ i y) (θ, fun j => t j.1)) else 0 := by
    by_cases h : t i = s
    · simp only [h, and_true, ite_true, Finset.mul_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl; intro e _; split_ifs <;> simp
    · simp [h]
  simp_rw [hs]
  exact sum_own_type ψ (fun θ t => ∑ e, if e i = z then ruleCombination ρ σ θ t e else 0)
    i s (fun c => quadraticScore (originalBelief ψ π i s) c -
      quadraticScore (testReport ψ π δ i y) c)

end BayesCorrelated.OrderImplementation
