module
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Basic.Real.Basic

@[expose] public section
open scoped BigOperators
namespace BayesCorrelated
universe uI uΘ uA uT uE
variable {I : Type uI} {Θ : Type uΘ} {A : I → Type uA} {T : I → Type uT}
variable [Fintype I] [DecidableEq I] [Fintype Θ]
variable [∀ i, Fintype (A i)] [∀ i, DecidableEq (A i)]
variable [∀ i, Fintype (T i)] [∀ i, DecidableEq (T i)]

/-- A finite probability mass function, with zero masses allowed. -/
def IsProbability {X : Type*} [Fintype X] (p : X → ℝ) : Prop :=
  (∀ x, 0 ≤ p x) ∧ ∑ x, p x = 1

/-- A state-dependent original information kernel. -/
def IsInformation (π : Θ → (∀ i, T i) → ℝ) : Prop := ∀ θ, IsProbability (π θ)

/-- A distribution over heterogeneous action profiles at every state and signal profile. -/
def IsDecisionRule (σ : Θ → (∀ i, T i) → (∀ i, A i) → ℝ) : Prop :=
  ∀ θ t, IsProbability (σ θ t)

/-- Weighted obedience gain, including every state, original signal and action profile. -/
noncomputable def obedienceGain (ψ : Θ → ℝ) (π : Θ → (∀ i, T i) → ℝ)
    (u : I → (∀ i, A i) → Θ → ℝ) (σ : Θ → (∀ i, T i) → (∀ i, A i) → ℝ)
    (i : I) (s : T i) (x y : A i) : ℝ :=
  ∑ θ, ∑ t, ∑ a, if t i = s ∧ a i = x then
    ψ θ * π θ t * σ θ t a * (u i a θ - u i (Function.update a i y) θ) else 0

/-- Obedience is imposed without division, including at null signal/recommendation events. -/
def BCE (ψ : Θ → ℝ) (π : Θ → (∀ i, T i) → ℝ)
    (u : I → (∀ i, A i) → Θ → ℝ) (σ : Θ → (∀ i, T i) → (∀ i, A i) → ℝ) : Prop :=
  ∀ i s x y, 0 ≤ obedienceGain ψ π u σ i s x y

variable {E : I → Type uE} [∀ i, Fintype (E i)] [∀ i, DecidableEq (E i)]

/-- Joint expansion kernel; its original-signal marginal is exactly π in every state. -/
def IsExpansion (π : Θ → (∀ i, T i) → ℝ)
    (q : Θ → (∀ i, T i) → (∀ i, E i) → ℝ) : Prop :=
  (∀ θ t e, 0 ≤ q θ t e) ∧ (∀ θ t, ∑ e, q θ t e = π θ t)

/-- Independent behavioral randomizations conditional on each player's full private signal. -/
def IsStrategy (β : ∀ i, T i → E i → A i → ℝ) : Prop :=
  ∀ i s z, IsProbability (β i s z)

noncomputable def strategyProduct (β : ∀ i, T i → E i → A i → ℝ)
    (t : ∀ i, T i) (e : ∀ i, E i) (a : ∀ i, A i) : ℝ :=
  ∏ i, β i (t i) (e i) (a i)

/-- Exact joint-law induction. Values of σ on π-null fibers are unconstrained by induction. -/
def Induces (π : Θ → (∀ i, T i) → ℝ)
    (σ : Θ → (∀ i, T i) → (∀ i, A i) → ℝ)
    (q : Θ → (∀ i, T i) → (∀ i, E i) → ℝ)
    (β : ∀ i, T i → E i → A i → ℝ) : Prop :=
  ∀ θ t a, π θ t * σ θ t a = ∑ e, q θ t e * strategyProduct β t e a

/-- Unnormalized expected payoff gain of pure action x against independently mixed opponents.
The action sum fixes the own coordinate to x, so it counts each opponent profile once. -/
noncomputable def bestResponseGain (ψ : Θ → ℝ)
    (u : I → (∀ i, A i) → Θ → ℝ)
    (q : Θ → (∀ i, T i) → (∀ i, E i) → ℝ)
    (β : ∀ i, T i → E i → A i → ℝ)
    (i : I) (s : T i) (z : E i) (x y : A i) : ℝ :=
  ∑ θ, ∑ t, ∑ e, ∑ a, if t i = s ∧ e i = z ∧ a i = x then
    ψ θ * q θ t e * (∏ j ∈ Finset.univ.erase i, β j (t j) (e j) (a j)) *
      (u i a θ - u i (Function.update a i y) θ) else 0

/-- Standard mixed BNE: every action played with positive probability is a best response. -/
def MixedBNE (ψ : Θ → ℝ) (u : I → (∀ i, A i) → Θ → ℝ)
    (q : Θ → (∀ i, T i) → (∀ i, E i) → ℝ)
    (β : ∀ i, T i → E i → A i → ℝ) : Prop :=
  ∀ i s z x y, 0 < β i s z x → 0 ≤ bestResponseGain ψ u q β i s z x y

/-- Finite expansion implementation; the existential allows arbitrary finite extra signals. -/
def Implementable (ψ : Θ → ℝ) (π : Θ → (∀ i, T i) → ℝ)
    (u : I → (∀ i, A i) → Θ → ℝ)
    (σ : Θ → (∀ i, T i) → (∀ i, A i) → ℝ) : Prop :=
  ∃ (E : I → Type uA) (_ : ∀ i, Fintype (E i)) (_ : ∀ i, DecidableEq (E i))
    (q : Θ → (∀ i, T i) → (∀ i, E i) → ℝ) (β : ∀ i, T i → E i → A i → ℝ),
    IsExpansion π q ∧ IsStrategy β ∧ MixedBNE ψ u q β ∧ Induces π σ q β
end BayesCorrelated
