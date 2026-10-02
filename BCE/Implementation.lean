module
public import BCE.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.NormNum
@[expose] public section
open scoped BigOperators
namespace BayesCorrelated.Implementation
open BayesCorrelated
universe uI uΘ uA uT uE
variable {I : Type uI} {Θ : Type uΘ} {A : I → Type uA} {T : I → Type uT}
variable [Fintype I] [DecidableEq I] [Fintype Θ]
variable [∀ i, Fintype (A i)] [∀ i, DecidableEq (A i)]
variable [∀ i, Fintype (T i)] [∀ i, DecidableEq (T i)]
variable {E : I → Type uE} [∀ i, Fintype (E i)] [∀ i, DecidableEq (E i)]

noncomputable def expandedGain (ψ : Θ → ℝ) (u : I → (∀ i, A i) → Θ → ℝ)
    (q : Θ → (∀ i, T i) → (∀ i, E i) → ℝ)
    (β : ∀ i, T i → E i → A i → ℝ)
    (i : I) (s : T i) (z : E i) (x y : A i) : ℝ :=
  ∑ θ, ∑ t, ∑ e, ∑ a, if t i = s ∧ e i = z ∧ a i = x then
    ψ θ * q θ t e * strategyProduct β t e a *
      (u i a θ - u i (Function.update a i y) θ) else 0

theorem expandedGain_factor (ψ : Θ → ℝ) (u : I → (∀ i, A i) → Θ → ℝ)
    (q : Θ → (∀ i, T i) → (∀ i, E i) → ℝ)
    (β : ∀ i, T i → E i → A i → ℝ) (i : I) (s : T i) (z : E i) (x y : A i) :
    expandedGain ψ u q β i s z x y = β i s z x * bestResponseGain ψ u q β i s z x y := by
  simp only [expandedGain, bestResponseGain, Finset.mul_sum]
  apply Finset.sum_congr rfl; intro θ _
  apply Finset.sum_congr rfl; intro t _
  apply Finset.sum_congr rfl; intro e _
  apply Finset.sum_congr rfl; intro a _
  split_ifs with h
  · rcases h with ⟨ht, he, ha⟩
    have hp := Finset.mul_prod_erase Finset.univ (fun j => β j (t j) (e j) (a j))
      (Finset.mem_univ i)
    dsimp [strategyProduct]
    rw [← hp, ht, he, ha]
    ring
  · simp

theorem expandedGain_nonneg (ψ : Θ → ℝ) (u : I → (∀ i, A i) → Θ → ℝ)
    (q : Θ → (∀ i, T i) → (∀ i, E i) → ℝ)
    (β : ∀ i, T i → E i → A i → ℝ) (hβ : IsStrategy β) (hB : MixedBNE ψ u q β)
    (i : I) (s : T i) (z : E i) (x y : A i) :
    0 ≤ expandedGain ψ u q β i s z x y := by
  rw [expandedGain_factor]
  have hn := (hβ i s z).1 x
  rcases eq_or_lt_of_le hn with h | h
  · rw [← h]; simp
  · exact mul_nonneg hn (hB i s z x y h)

theorem sum_expandedGain (ψ : Θ → ℝ) (π : Θ → (∀ i, T i) → ℝ)
    (u : I → (∀ i, A i) → Θ → ℝ) (σ : Θ → (∀ i, T i) → (∀ i, A i) → ℝ)
    (q : Θ → (∀ i, T i) → (∀ i, E i) → ℝ)
    (β : ∀ i, T i → E i → A i → ℝ) (hi : Induces π σ q β)
    (i : I) (s : T i) (x y : A i) :
    obedienceGain ψ π u σ i s x y = ∑ z, expandedGain ψ u q β i s z x y := by
  simp only [obedienceGain, expandedGain]
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro θ _
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro t _
  conv_rhs =>
    rw [Finset.sum_comm]
    arg 2; ext e; rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro a _
  by_cases ht : t i = s
  · by_cases ha : a i = x
    · simp only [ht, ha, true_and, and_true, ite_true]
      simp only [mul_assoc, hi θ t a, Finset.mul_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl; intro e _
      simp [eq_comm]
    · simp [ha]
  · simp [ht]

/-- Reverse direction for arbitrary finite expansion spaces and genuinely mixed strategies. -/
theorem mixedBNE_induces_BCE (ψ : Θ → ℝ) (π : Θ → (∀ i, T i) → ℝ)
    (u : I → (∀ i, A i) → Θ → ℝ) (σ : Θ → (∀ i, T i) → (∀ i, A i) → ℝ)
    (q : Θ → (∀ i, T i) → (∀ i, E i) → ℝ)
    (β : ∀ i, T i → E i → A i → ℝ)
    (hβ : IsStrategy β) (hB : MixedBNE ψ u q β) (hi : Induces π σ q β) : BCE ψ π u σ := by
  intro i s x y
  rw [sum_expandedGain ψ π u σ q β hi]
  exact Finset.sum_nonneg fun z _ => expandedGain_nonneg ψ u q β hβ hB i s z x y

noncomputable def recommendationKernel (π : Θ → (∀ i, T i) → ℝ)
    (σ : Θ → (∀ i, T i) → (∀ i, A i) → ℝ) :
    Θ → (∀ i, T i) → (∀ i, A i) → ℝ := fun θ t a => π θ t * σ θ t a

noncomputable def follow : ∀ i, T i → A i → A i → ℝ := fun _ _ z x => if x = z then 1 else 0

omit [Fintype I] [DecidableEq I] [∀ i, Fintype (T i)] [∀ i, DecidableEq (T i)] in
theorem follow_isStrategy : IsStrategy (follow (T := T) (A := A)) := by
  intro i s z
  constructor
  · intro x; dsimp [follow]; split <;> norm_num
  · simp [follow]

omit [DecidableEq I] [∀ i, Fintype (A i)] [∀ i, Fintype (T i)] [∀ i, DecidableEq (T i)] in
theorem follow_product (t : ∀ i, T i) (e a : ∀ i, A i) :
    strategyProduct follow t e a = if a = e then 1 else 0 := by
  classical
  by_cases h : a = e
  · subst a; simp [strategyProduct, follow]
  · have hn : ∃ i, a i ≠ e i := by simpa [funext_iff] using h
    obtain ⟨i, hi⟩ := hn
    rw [ite_eq_right h]
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [follow, hi])

omit [Fintype Θ] [∀ i, DecidableEq (A i)] [∀ i, DecidableEq (T i)] in
theorem recommendation_isExpansion (π : Θ → (∀ i, T i) → ℝ)
    (σ : Θ → (∀ i, T i) → (∀ i, A i) → ℝ)
    (hπ : IsInformation π) (hσ : IsDecisionRule σ) : IsExpansion π (recommendationKernel π σ) := by
  constructor
  · intro θ t a; exact mul_nonneg ((hπ θ).1 t) ((hσ θ t).1 a)
  · intro θ t; simp [recommendationKernel, ← Finset.mul_sum, (hσ θ t).2]

omit [Fintype Θ] in
theorem recommendation_induces (π : Θ → (∀ i, T i) → ℝ)
    (σ : Θ → (∀ i, T i) → (∀ i, A i) → ℝ) :
    Induces π σ (recommendationKernel π σ) follow := by
  intro θ t a
  simp [follow_product, recommendationKernel]

theorem recommendation_expandedGain (ψ : Θ → ℝ) (π : Θ → (∀ i, T i) → ℝ)
    (u : I → (∀ i, A i) → Θ → ℝ) (σ : Θ → (∀ i, T i) → (∀ i, A i) → ℝ)
    (i : I) (s : T i) (x y : A i) :
    expandedGain ψ u (recommendationKernel π σ) follow i s x x y =
      obedienceGain ψ π u σ i s x y := by
  simp only [expandedGain, obedienceGain]
  apply Finset.sum_congr rfl; intro θ _
  apply Finset.sum_congr rfl; intro t _
  simp_rw [follow_product]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro a _
  classical
  rw [Finset.sum_eq_single a]
  · simp [recommendationKernel, mul_assoc, and_self]
  · intro b _ hba
    simp [Ne.symm hba]
  · simp

/-- Forward construction uses action recommendations as each player's finite extra signal. -/
theorem recommendation_mixedBNE (ψ : Θ → ℝ) (π : Θ → (∀ i, T i) → ℝ)
    (u : I → (∀ i, A i) → Θ → ℝ) (σ : Θ → (∀ i, T i) → (∀ i, A i) → ℝ)
    (h : BCE ψ π u σ) : MixedBNE ψ u (recommendationKernel π σ) follow := by
  intro i s z x y hx
  have he : x = z := by by_contra hn; simp [follow, hn] at hx
  subst z
  have hf := expandedGain_factor ψ u (recommendationKernel π σ) follow i s x x y
  simp only [follow, ite_true, one_mul] at hf
  rw [← hf, recommendation_expandedGain]
  exact h i s x y

/-- Bergemann–Morris Theorem 1, with no full-support prior assumption. -/
theorem finite_characterization (ψ : Θ → ℝ) (π : Θ → (∀ i, T i) → ℝ)
    (u : I → (∀ i, A i) → Θ → ℝ) (σ : Θ → (∀ i, T i) → (∀ i, A i) → ℝ)
    (_hψ : IsProbability ψ) (hπ : IsInformation π) (hσ : IsDecisionRule σ) :
    BCE ψ π u σ ↔ Implementable ψ π u σ := by
  constructor
  · intro h
    exact ⟨A, inferInstance, inferInstance, recommendationKernel π σ, follow,
      recommendation_isExpansion π σ hπ hσ, follow_isStrategy,
      recommendation_mixedBNE ψ π u σ h, recommendation_induces π σ⟩
  · rintro ⟨E, hE, dE, q, β, _, hβ, hB, hi⟩
    exact mixedBNE_induces_BCE ψ π u σ q β hβ hB hi
end BayesCorrelated.Implementation
