module
public import BCE.OrderDefs
public import BCE.Support
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith

@[expose] public section
open scoped BigOperators
namespace BayesCorrelated.OrderImplementation
open BayesCorrelated
universe uI uΘ uA uT uE
variable {I : Type uI} {Θ : Type uΘ} {A : I → Type uA}
variable {T : I → Type uT} {E : I → Type uE}
variable [Fintype I] [DecidableEq I] [Fintype Θ]
variable [∀ i, Fintype (A i)] [∀ i, DecidableEq (A i)]
variable [∀ i, Fintype (T i)] [∀ i, DecidableEq (T i)]
variable [∀ i, Fintype (E i)] [∀ i, DecidableEq (E i)]

noncomputable def transferJoint (q : Θ → (∀ i, T i) → (∀ i, E i) → ℝ)
    (σ : Θ → (∀ i, T i) → (∀ i, A i) → ℝ) (θ : Θ) (e : ∀ i, E i)
    (a : ∀ i, A i) : ℝ := ∑ t, q θ t e * σ θ t a

theorem transferJoint_nonneg (π : Θ → (∀ i, T i) → ℝ)
    (ρ : Θ → (∀ i, E i) → ℝ) (q : Θ → (∀ i, T i) → (∀ i, E i) → ℝ)
    (σ : Θ → (∀ i, T i) → (∀ i, A i) → ℝ)
    (hq : IsCombination π ρ q) (hσ : IsDecisionRule σ) (θ : Θ) (e : ∀ i, E i)
    (a : ∀ i, A i) : 0 ≤ transferJoint q σ θ e a :=
  Finset.sum_nonneg fun t _ => mul_nonneg (hq.1.1 θ t e) ((hσ θ t).1 a)

theorem transferJoint_sum (π : Θ → (∀ i, T i) → ℝ)
    (ρ : Θ → (∀ i, E i) → ℝ) (q : Θ → (∀ i, T i) → (∀ i, E i) → ℝ)
    (σ : Θ → (∀ i, T i) → (∀ i, A i) → ℝ)
    (hq : IsCombination π ρ q) (hσ : IsDecisionRule σ) (θ : Θ) (e : ∀ i, E i) :
    ∑ a, transferJoint q σ θ e a = ρ θ e := by
  simp only [transferJoint]
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum, (hσ _ _).2, mul_one]
  exact hq.2 θ e

theorem combination_null_right (π : Θ → (∀ i, T i) → ℝ)
    (ρ : Θ → (∀ i, E i) → ℝ) (q : Θ → (∀ i, T i) → (∀ i, E i) → ℝ)
    (hq : IsCombination π ρ q) (θ : Θ) (e : ∀ i, E i) (h : ρ θ e = 0)
    (t : ∀ i, T i) : q θ t e = 0 := by
  apply (Finset.sum_eq_zero_iff_of_nonneg (fun t _ => hq.1.1 θ t e)).mp
    ((hq.2 θ e).trans h) t (Finset.mem_univ t)

noncomputable def transferredRule (ρ : Θ → (∀ i, E i) → ℝ)
    (q : Θ → (∀ i, T i) → (∀ i, E i) → ℝ)
    (σ : Θ → (∀ i, T i) → (∀ i, A i) → ℝ) (a₀ : ∀ i, A i)
    (θ : Θ) (e : ∀ i, E i) (a : ∀ i, A i) : ℝ :=
  if ρ θ e = 0 then (if a = a₀ then 1 else 0) else transferJoint q σ θ e a / ρ θ e

theorem transferredRule_joint (π : Θ → (∀ i, T i) → ℝ)
    (ρ : Θ → (∀ i, E i) → ℝ) (q : Θ → (∀ i, T i) → (∀ i, E i) → ℝ)
    (σ : Θ → (∀ i, T i) → (∀ i, A i) → ℝ) (a₀ : ∀ i, A i)
    (hq : IsCombination π ρ q) (θ : Θ) (e : ∀ i, E i) (a : ∀ i, A i) :
    ρ θ e * transferredRule ρ q σ a₀ θ e a = transferJoint q σ θ e a := by
  by_cases h : ρ θ e = 0
  · simp [transferredRule, h, transferJoint, combination_null_right π ρ q hq θ e h]
  · simp [transferredRule, h, mul_div_cancel₀]

theorem transferredRule_valid (π : Θ → (∀ i, T i) → ℝ)
    (ρ : Θ → (∀ i, E i) → ℝ) (q : Θ → (∀ i, T i) → (∀ i, E i) → ℝ)
    (σ : Θ → (∀ i, T i) → (∀ i, A i) → ℝ) (a₀ : ∀ i, A i)
    (hρ : IsInformation ρ) (hq : IsCombination π ρ q) (hσ : IsDecisionRule σ) :
    IsDecisionRule (transferredRule ρ q σ a₀) := by
  intro θ e
  by_cases h : ρ θ e = 0
  · constructor
    · intro a; simp only [transferredRule, h, ite_true]; split_ifs <;> norm_num
    · simp [transferredRule, h]
  · constructor
    · intro a
      simpa only [transferredRule, h, ite_false] using
        div_nonneg (transferJoint_nonneg π ρ q σ hq hσ θ e a) ((hρ θ).1 e)
    · simp only [transferredRule, h, ite_false]
      simp only [div_eq_mul_inv]
      rw [← Finset.sum_mul, transferJoint_sum π ρ q σ hq hσ, mul_inv_cancel₀ h]

theorem transferredRule_outcome (π : Θ → (∀ i, T i) → ℝ)
    (ρ : Θ → (∀ i, E i) → ℝ) (q : Θ → (∀ i, T i) → (∀ i, E i) → ℝ)
    (σ : Θ → (∀ i, T i) → (∀ i, A i) → ℝ) (a₀ : ∀ i, A i)
    (hq : IsCombination π ρ q) : outcome ρ (transferredRule ρ q σ a₀) = outcome π σ := by
  funext θ a
  simp only [outcome, transferredRule_joint π ρ q σ a₀ hq, transferJoint]
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_mul, hq.1.2]

theorem transferredRule_gain (ψ : Θ → ℝ) (π : Θ → (∀ i, T i) → ℝ)
    (ρ : Θ → (∀ i, E i) → ℝ) (q : Θ → (∀ i, T i) → (∀ i, E i) → ℝ)
    (σ : Θ → (∀ i, T i) → (∀ i, A i) → ℝ) (a₀ : ∀ i, A i)
    (u : I → (∀ i, A i) → Θ → ℝ) (φ : ∀ i, T i → E i → ℝ)
    (hq : IsCombination π ρ q) (hφ : HasIndividualChannels π q φ)
    (i : I) (z : E i) (x y : A i) :
    obedienceGain ψ ρ u (transferredRule ρ q σ a₀) i z x y =
      ∑ s, φ i s z * obedienceGain ψ π u σ i s x y := by
  classical
  have term (θ : Θ) (e : ∀ i, E i) (a : ∀ i, A i) :
      ψ θ * ρ θ e * transferredRule ρ q σ a₀ θ e a *
        (u i a θ - u i (Function.update a i y) θ) =
      ∑ t, ψ θ * q θ t e * σ θ t a *
        (u i a θ - u i (Function.update a i y) θ) := by
    rw [show ψ θ * ρ θ e * transferredRule ρ q σ a₀ θ e a *
        (u i a θ - u i (Function.update a i y) θ) =
      ψ θ * (ρ θ e * transferredRule ρ q σ a₀ θ e a) *
        (u i a θ - u i (Function.update a i y) θ) by ring]
    rw [transferredRule_joint π ρ q σ a₀ hq]
    simp only [transferJoint, Finset.mul_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl; intro t _; ring
  simp only [obedienceGain, term, Finset.ite_sum_zero]
  conv_lhs =>
    arg 2; ext θ
    rw [Finset.sum_comm]
    arg 2; ext a
    rw [Finset.sum_comm]
    arg 2; ext t
    rw [show (∑ e, if e i = z ∧ a i = x then
      ψ θ * q θ t e * σ θ t a * (u i a θ - u i (Function.update a i y) θ) else 0) =
      if a i = x then ψ θ * σ θ t a *
        (u i a θ - u i (Function.update a i y) θ) *
        (∑ e, if e i = z then q θ t e else 0) else 0 by
      by_cases ha : a i = x
      · simp only [ha, and_true, ite_true, Finset.mul_sum]
        apply Finset.sum_congr rfl; intro e _
        split_ifs <;> ring
      · simp [ha]]
    rw [hφ.2 i θ t z]
  conv_lhs => arg 2; ext θ; rw [Finset.sum_comm]
  simp only [Finset.mul_sum]
  conv_rhs => rw [Finset.sum_comm]; arg 2; ext θ; rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro θ _
  apply Finset.sum_congr rfl; intro t _
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro a _
  by_cases ha : a i = x
  · simp only [ha, and_true, ite_true]
    rw [show (∑ s, φ i s z * (if t i = s then
      ψ θ * π θ t * σ θ t a * (u i a θ - u i (Function.update a i y) θ) else 0)) =
      φ i (t i) z * (ψ θ * π θ t * σ θ t a *
        (u i a θ - u i (Function.update a i y) θ)) by
      simp [mul_ite, eq_comm]]
    ring
  · simp [ha]

theorem transferredRule_BCE (ψ : Θ → ℝ) (π : Θ → (∀ i, T i) → ℝ)
    (ρ : Θ → (∀ i, E i) → ℝ) (q : Θ → (∀ i, T i) → (∀ i, E i) → ℝ)
    (σ : Θ → (∀ i, T i) → (∀ i, A i) → ℝ) (a₀ : ∀ i, A i)
    (u : I → (∀ i, A i) → Θ → ℝ) (φ : ∀ i, T i → E i → ℝ)
    (hq : IsCombination π ρ q) (hφ : HasIndividualChannels π q φ)
    (hb : BCE ψ π u σ) : BCE ψ ρ u (transferredRule ρ q σ a₀) := by
  intro i z x y
  rw [transferredRule_gain ψ π ρ q σ a₀ u φ hq hφ]
  exact Finset.sum_nonneg fun s _ => mul_nonneg ((hφ.1 i s).1 z) (hb i s x y)

theorem probability_nonempty {X : Type*} [Fintype X] (p : X → ℝ)
    (hp : IsProbability p) : Nonempty X := by
  classical
  by_contra h
  haveI : IsEmpty X := not_nonempty_iff.mp h
  have := hp.2
  simp at this

theorem individuallySufficient_outcome [Nonempty Θ]
    (ψ : Θ → ℝ) (π : Θ → (∀ i, T i) → ℝ) (ρ : Θ → (∀ i, E i) → ℝ)
    (hπ : IsInformation π) (hρ : IsInformation ρ)
    (hs : IndividuallySufficient π ρ)
    (u : I → (∀ i, A i) → Θ → ℝ) (ν : Θ → (∀ i, A i) → ℝ)
    (hv : IsBCEOutcome ψ π u ν) : IsBCEOutcome ψ ρ u ν := by
  classical
  obtain ⟨q, φ, hq, hφ⟩ := hs
  obtain ⟨σ, hσ, hb, he⟩ := hv
  let θ₀ : Θ := Classical.arbitrary Θ
  letI := probability_nonempty (π θ₀) (hπ θ₀)
  let t₀ : ∀ i, T i := Classical.arbitrary _
  letI := probability_nonempty (σ θ₀ t₀) (hσ θ₀ t₀)
  let a₀ : ∀ i, A i := Classical.arbitrary _
  exact ⟨transferredRule ρ q σ a₀, transferredRule_valid π ρ q σ a₀ hρ hq hσ,
    transferredRule_BCE ψ π ρ q σ a₀ u φ hq hφ hb,
    (transferredRule_outcome π ρ q σ a₀ hq).trans he⟩

theorem individuallySufficient_moreIncentiveConstrained [Nonempty Θ]
    (π : Θ → (∀ i, T i) → ℝ) (ρ : Θ → (∀ i, E i) → ℝ)
    (hπ : IsInformation π) (hρ : IsInformation ρ)
    (hs : IndividuallySufficient π ρ) : MoreIncentiveConstrained π ρ := by
  intro A _ _ ψ _ u ν hv
  exact individuallySufficient_outcome ψ π ρ hπ hρ hs u ν hv

end BayesCorrelated.OrderImplementation
