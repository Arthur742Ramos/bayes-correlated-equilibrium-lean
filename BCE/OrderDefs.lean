module
public import BCE.Defs

@[expose] public section
open scoped BigOperators
namespace BayesCorrelated
universe uI uΘ uA uT uE
variable {I : Type uI} {Θ : Type uΘ} {T : I → Type uT} {E : I → Type uE}
variable [Fintype I] [DecidableEq I] [Fintype Θ]
variable [∀ i, Fintype (T i)] [∀ i, DecidableEq (T i)]
variable [∀ i, Fintype (E i)] [∀ i, DecidableEq (E i)]

/-- A combination preserves both information marginals, separately in every state. -/
def IsCombination (π : Θ → (∀ i, T i) → ℝ) (ρ : Θ → (∀ i, E i) → ℝ)
    (q : Θ → (∀ i, T i) → (∀ i, E i) → ℝ) : Prop :=
  IsExpansion π q ∧ ∀ θ e, ∑ t, q θ t e = ρ θ e

/-- The conditional channel of player i depends only on that player's original signal.
This is a marginal condition; the joint coupling need not be a product of channels. -/
def HasIndividualChannels (π : Θ → (∀ i, T i) → ℝ)
    (q : Θ → (∀ i, T i) → (∀ i, E i) → ℝ)
    (φ : ∀ i, T i → E i → ℝ) : Prop :=
  (∀ i s, IsProbability (φ i s)) ∧
  ∀ i θ t z, (∑ e, if e i = z then q θ t e else 0) = π θ t * φ i (t i) z

/-- Weighted individual sufficiency, with no conditional division on null events. -/
def IndividuallySufficient (π : Θ → (∀ i, T i) → ℝ)
    (ρ : Θ → (∀ i, E i) → ℝ) : Prop :=
  ∃ q φ, IsCombination π ρ q ∧ HasIndividualChannels π q φ

/-- Strict positivity of every state of a normalized common prior. -/
def FullSupportPrior (ψ : Θ → ℝ) : Prop := IsProbability ψ ∧ ∀ θ, 0 < ψ θ

variable {A : I → Type uA} [∀ i, Fintype (A i)] [∀ i, DecidableEq (A i)]

/-- The action distribution conditional on the state, after original signals are integrated out. -/
noncomputable def outcome (π : Θ → (∀ i, T i) → ℝ)
    (σ : Θ → (∀ i, T i) → (∀ i, A i) → ℝ) : Θ → (∀ i, A i) → ℝ :=
  fun θ a => ∑ t, π θ t * σ θ t a

/-- Actual BCE outcome: a normalized decision rule satisfying all weighted obedience inequalities. -/
def IsBCEOutcome (ψ : Θ → ℝ) (π : Θ → (∀ i, T i) → ℝ)
    (u : I → (∀ i, A i) → Θ → ℝ) (ν : Θ → (∀ i, A i) → ℝ) : Prop :=
  ∃ σ, IsDecisionRule σ ∧ BCE ψ π u σ ∧ outcome π σ = ν

/-- All finite basic games on the fixed players and states, including arbitrary heterogeneous
action spaces and real utility functions. The universe contains both signal spaces. -/
def MoreIncentiveConstrained (π : Θ → (∀ i, T i) → ℝ)
    (ρ : Θ → (∀ i, E i) → ℝ) : Prop :=
  ∀ (A : I → Type (max uI uΘ uT uE))
    (_ : ∀ i, Fintype (A i)) (_ : ∀ i, DecidableEq (A i))
    (ψ : Θ → ℝ), FullSupportPrior ψ →
    ∀ (u : I → (∀ i, A i) → Θ → ℝ) (ν : Θ → (∀ i, A i) → ℝ),
      IsBCEOutcome ψ π u ν → IsBCEOutcome ψ ρ u ν
end BayesCorrelated
