module
public import BCE.OnePlayer
public import Mathlib.Data.Fintype.BigOperators
@[expose] public section
open scoped BigOperators
namespace BayesCorrelated.Examples
open BayesCorrelated BayesCorrelated.Implementation

section Dominance
variable {I Θ : Type*} {A T : I → Type*}
variable [Fintype I] [DecidableEq I] [Fintype Θ]
variable [∀ i, Fintype (A i)] [∀ i, DecidableEq (A i)]
variable [∀ i, Fintype (T i)] [∀ i, DecidableEq (T i)]

/-- Pointwise optimal supported recommendations provide a useful, nonvacuous BCE certificate. -/
theorem bce_of_supported_dominance (ψ : Θ → ℝ) (π : Θ → (∀ i, T i) → ℝ)
    (u : I → (∀ i, A i) → Θ → ℝ) (σ : Θ → (∀ i, T i) → (∀ i, A i) → ℝ)
    (hψ : IsProbability ψ) (hπ : IsInformation π) (hσ : IsDecisionRule σ)
    (hu : ∀ θ t a i y, 0 < σ θ t a → u i (Function.update a i y) θ ≤ u i a θ) :
    BCE ψ π u σ := by
  intro i s x y
  apply Finset.sum_nonneg; intro θ _
  apply Finset.sum_nonneg; intro t _
  apply Finset.sum_nonneg; intro a _
  split_ifs with h
  · have hs := (hσ θ t).1 a
    rcases eq_or_lt_of_le hs with hz | hp
    · rw [← hz]; simp
    · exact mul_nonneg (mul_nonneg (mul_nonneg (hψ.1 θ) ((hπ θ).1 t)) hs)
        (sub_nonneg.mpr (hu θ t a i y hp))
  · exact le_rfl
end Dominance

/-- Binary state matching: a receiver initially sees no information, then learns the state. -/
noncomputable def binaryPrior : Bool → ℝ := fun _ => 1 / 2
noncomputable def nullSignal : Bool → Bool → ℝ := fun _ s => if s = false then 1 else 0
noncomputable def matchUtility (a θ : Bool) : ℝ := if a = θ then 1 else 0
noncomputable def revealRule : Bool → Bool → Bool → ℝ := fun θ _ a => if a = θ then 1 else 0

theorem binaryPrior_valid : IsProbability binaryPrior := by
  constructor
  · intro θ; norm_num [binaryPrior]
  · norm_num [binaryPrior, Fintype.sum_bool]

theorem nullSignal_valid (θ : Bool) : IsProbability (nullSignal θ) := by
  constructor
  · intro s; dsimp [nullSignal]; split_ifs <;> norm_num
  · simp [nullSignal]

theorem revealRule_valid (θ s : Bool) : IsProbability (revealRule θ s) := by
  constructor
  · intro a; dsimp [revealRule]; split_ifs <;> norm_num
  · simp [revealRule]

/-- Both obedience and expansion implementation for full revelation, including the null signal true. -/
theorem binary_revelation_implementable :
    Implementable (I := Unit) (A := fun _ => Bool) (T := fun _ => Bool)
      binaryPrior (fun θ t => nullSignal θ (t ())) (fun _ a θ => matchUtility (a ()) θ)
      (fun θ t a => revealRule θ (t ()) (a ())) := by
  apply (onePlayer_characterization binaryPrior nullSignal matchUtility revealRule
    binaryPrior_valid nullSignal_valid revealRule_valid).mp
  intro s x y
  apply Finset.sum_nonneg; intro θ _
  by_cases hx : x = θ
  · subst x
    have hy : matchUtility y θ ≤ 1 := by dsimp [matchUtility]; split_ifs <;> norm_num
    exact mul_nonneg (mul_nonneg (mul_nonneg (binaryPrior_valid.1 θ)
      ((nullSignal_valid θ).1 s)) ((revealRule_valid θ s).1 θ)) (by simpa [matchUtility] using sub_nonneg.mpr hy)
  · simp [revealRule, hx]

/-- A recommendation to choose the opposite state fails obedience at the positive signal. -/
theorem wrong_recommendation_not_obedient :
    ¬ (∀ s x y : Bool, 0 ≤ ∑ θ, binaryPrior θ * nullSignal θ s *
      (if x = !θ then (1 : ℝ) else 0) * (matchUtility x θ - matchUtility y θ)) := by
  intro h
  have hn := h false false true
  norm_num [binaryPrior, nullSignal, matchUtility, Fintype.sum_bool] at hn

/-- Two players receive correlated private recommendations in a coordination game. -/
noncomputable def coordinationRule (θ : Bool) (_t : Bool → Unit) (a : Bool → Bool) : ℝ :=
  if a = (fun _ => θ) then 1 else 0
noncomputable def coordinationUtility (_i : Bool) (a : Bool → Bool) (_θ : Bool) : ℝ :=
  if a false = a true then 1 else 0

theorem coordination_rule_valid : IsDecisionRule coordinationRule := by
  intro θ t
  constructor
  · intro a; dsimp [coordinationRule]; split_ifs <;> norm_num
  · simp [coordinationRule]

theorem coordination_information_valid :
    IsInformation (T := fun _ : Bool => Unit) (fun _θ : Bool => fun _t => (1 : ℝ)) := by
  intro θ
  constructor
  · intro t; norm_num
  · simp

/-- A fair common recommendation coordinates the players, although their original signals are null. -/
theorem coordination_implementable :
    Implementable binaryPrior (fun _θ : Bool => fun _t : Bool → Unit => (1 : ℝ))
      coordinationUtility coordinationRule := by
  apply (finite_characterization _ _ _ _ binaryPrior_valid coordination_information_valid
    coordination_rule_valid).mp
  apply bce_of_supported_dominance _ _ _ _ binaryPrior_valid coordination_information_valid
    coordination_rule_valid
  intro θ t a i y ha
  have he : a = (fun _ => θ) := by by_contra hn; simp [coordinationRule, hn] at ha
  subst a
  simp only [coordinationUtility, ite_true]
  split_ifs <;> norm_num

/-- Off-diagonal outcomes receive zero mass, so recommendations are correlated. -/
theorem coordination_off_diagonal (a : Bool → Bool) (h : a false ≠ a true) :
    ∑ θ, binaryPrior θ * coordinationRule θ (fun _ => ()) a = 0 := by
  apply Finset.sum_eq_zero; intro θ _
  have hn : a ≠ (fun _ => θ) := by intro he; apply h; simp [he]
  simp [coordinationRule, hn]

/-- Both diagonal outcomes have probability one half. -/
theorem coordination_diagonal (b : Bool) :
    ∑ θ, binaryPrior θ * coordinationRule θ (fun _ => ()) (fun _ => b) = 1 / 2 := by
  have he : ∀ θ : Bool, ((fun _ : Bool => b) = (fun _ : Bool => θ)) ↔ b = θ := by
    intro θ; constructor
    · intro h; exact congrFun h false
    · intro h; rw [h]
  simp [coordinationRule, he, binaryPrior]
end BayesCorrelated.Examples
