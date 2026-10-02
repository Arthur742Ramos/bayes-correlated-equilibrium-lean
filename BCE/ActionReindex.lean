module
public import BCE.OrderTransport
public import Mathlib.Logic.Equiv.Prod
public import Mathlib.Data.Fintype.EquivFin

@[expose] public section
open scoped BigOperators
namespace BayesCorrelated.OrderImplementation
open BayesCorrelated
universe uI uΘ uT uA uB uE
variable {I : Type uI} {Θ : Type uΘ} {T : I → Type uT}
variable {A : I → Type uA} {B : I → Type uB}
variable [Fintype I] [DecidableEq I] [Fintype Θ]
variable [∀ i, Fintype (T i)] [∀ i, DecidableEq (T i)]
variable [∀ i, Fintype (A i)] [∀ i, DecidableEq (A i)]
variable [∀ i, Fintype (B i)] [∀ i, DecidableEq (B i)]

def profileEquiv (e : ∀ i, A i ≃ B i) : (∀ i, A i) ≃ (∀ i, B i) := Equiv.piCongrRight e

theorem profileEquiv_update (e : ∀ i, A i ≃ B i) (a : ∀ i, A i) (i : I) (y : A i) :
    profileEquiv e (Function.update a i y) = Function.update (profileEquiv e a) i (e i y) := by
  funext j
  by_cases hj : j = i
  · subst j; simp [profileEquiv]
  · simp [profileEquiv, Function.update_of_ne hj]

noncomputable def reindexRule (e : ∀ i, A i ≃ B i)
    (σ : Θ → (∀ i, T i) → (∀ i, A i) → ℝ) :
    Θ → (∀ i, T i) → (∀ i, B i) → ℝ := fun θ t b => σ θ t ((profileEquiv e).symm b)

noncomputable def reindexUtility (e : ∀ i, A i ≃ B i)
    (u : I → (∀ i, A i) → Θ → ℝ) : I → (∀ i, B i) → Θ → ℝ :=
  fun i b θ => u i ((profileEquiv e).symm b) θ

theorem reindexRule_valid (e : ∀ i, A i ≃ B i)
    (σ : Θ → (∀ i, T i) → (∀ i, A i) → ℝ) (hσ : IsDecisionRule σ) :
    IsDecisionRule (reindexRule e σ) := by
  intro θ t
  constructor
  · intro b; exact (hσ θ t).1 _
  · exact ((profileEquiv e).symm.sum_comp (σ θ t)).trans (hσ θ t).2

theorem reindex_gain (e : ∀ i, A i ≃ B i) (ψ : Θ → ℝ)
    (π : Θ → (∀ i, T i) → ℝ) (u : I → (∀ i, A i) → Θ → ℝ)
    (σ : Θ → (∀ i, T i) → (∀ i, A i) → ℝ) (i : I) (s : T i) (x y : A i) :
    obedienceGain ψ π (reindexUtility e u) (reindexRule e σ) i s (e i x) (e i y) =
      obedienceGain ψ π u σ i s x y := by
  classical
  unfold obedienceGain
  apply Finset.sum_congr rfl; intro θ _
  apply Finset.sum_congr rfl; intro t _
  rw [← (profileEquiv e).sum_comp (fun b => if t i = s ∧ b i = e i x then
    ψ θ * π θ t * reindexRule e σ θ t b *
      (reindexUtility e u i b θ - reindexUtility e u i (Function.update b i (e i y)) θ) else 0)]
  apply Finset.sum_congr rfl; intro a _
  have hu : (profileEquiv e).symm (Function.update (profileEquiv e a) i (e i y)) =
      Function.update a i y := by
    rw [← profileEquiv_update, Equiv.symm_apply_apply]
  simp only [reindexRule, reindexUtility, Equiv.symm_apply_apply, hu]
  change (if t i = s ∧ e i (a i) = e i x then _ else _) = _
  simp only [(e i).injective.eq_iff]

theorem reindex_BCE (e : ∀ i, A i ≃ B i) (ψ : Θ → ℝ)
    (π : Θ → (∀ i, T i) → ℝ) (u : I → (∀ i, A i) → Θ → ℝ)
    (σ : Θ → (∀ i, T i) → (∀ i, A i) → ℝ) (hb : BCE ψ π u σ) :
    BCE ψ π (reindexUtility e u) (reindexRule e σ) := by
  intro i s x y
  obtain ⟨x', rfl⟩ := (e i).surjective x
  obtain ⟨y', rfl⟩ := (e i).surjective y
  rw [reindex_gain]
  exact hb i s x' y'

noncomputable def reindexOutcome (e : ∀ i, A i ≃ B i)
    (ν : Θ → (∀ i, A i) → ℝ) : Θ → (∀ i, B i) → ℝ :=
  fun θ b => ν θ ((profileEquiv e).symm b)

theorem reindex_outcome (e : ∀ i, A i ≃ B i) (ψ : Θ → ℝ)
    (π : Θ → (∀ i, T i) → ℝ) (u : I → (∀ i, A i) → Θ → ℝ)
    (ν : Θ → (∀ i, A i) → ℝ) (hv : IsBCEOutcome ψ π u ν) :
    IsBCEOutcome ψ π (reindexUtility e u) (reindexOutcome e ν) := by
  obtain ⟨σ, hσ, hb, he⟩ := hv
  refine ⟨reindexRule e σ, reindexRule_valid e σ hσ, reindex_BCE e ψ π u σ hb, ?_⟩
  funext θ b
  exact congr_fun (congr_fun he θ) ((profileEquiv e).symm b)

theorem profileEquiv_symm (e : ∀ i, A i ≃ B i) :
    profileEquiv (fun i => (e i).symm) = (profileEquiv e).symm := rfl

theorem reindexUtility_back (e : ∀ i, A i ≃ B i) (u : I → (∀ i, A i) → Θ → ℝ) :
    reindexUtility (fun i => (e i).symm) (reindexUtility e u) = u := by
  funext i a θ
  simp [reindexUtility, profileEquiv_symm]

theorem reindexOutcome_back (e : ∀ i, A i ≃ B i) (ν : Θ → (∀ i, A i) → ℝ) :
    reindexOutcome (fun i => (e i).symm) (reindexOutcome e ν) = ν := by
  funext θ a
  simp [reindexOutcome, profileEquiv_symm]

/-- The finite-game quantifier applies to action carriers in any Lean universe:
encode each finite action set by its cardinality and transfer through an equivalence. -/
theorem moreIncentiveConstrained_outcome_any_universe
    {E : I → Type uE} [∀ i, Fintype (E i)] [∀ i, DecidableEq (E i)]
    (ψ : Θ → ℝ) (π : Θ → (∀ i, T i) → ℝ) (ρ : Θ → (∀ i, E i) → ℝ)
    (ho : MoreIncentiveConstrained π ρ) (hψ : FullSupportPrior ψ)
    (u : I → (∀ i, A i) → Θ → ℝ) (ν : Θ → (∀ i, A i) → ℝ)
    (hv : IsBCEOutcome ψ π u ν) : IsBCEOutcome ψ ρ u ν := by
  classical
  let B : I → Type (max uI uΘ uT uE) := fun i =>
    ULift.{max uI uΘ uT uE} (Fin (Fintype.card (A i)))
  let e : ∀ i, A i ≃ B i := fun i => (Fintype.equivFin (A i)).trans Equiv.ulift.symm
  have hv' := reindex_outcome e ψ π u ν hv
  have hw := ho B (fun i => inferInstance) (fun i => inferInstance) ψ hψ
    (reindexUtility e u) (reindexOutcome e ν) hv'
  have hb := reindex_outcome (fun i => (e i).symm) ψ ρ _ _ hw
  simpa only [reindexUtility_back, reindexOutcome_back] using hb

end BayesCorrelated.OrderImplementation
