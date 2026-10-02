module
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Basic.Real.Basic

/-! Finite Bergemann–Morris Theorems 1 and 2. All twenty model definitions have their
exact implementation bodies. Only the thirteen selected theorem proofs are deliberate
reference placeholders. Solution imports the complete proved library. Null signals
use weighted inequalities; Theorem 1 permits zero-prior states. Theorem 2 ranges
over all finite basic games with full-support priors and assumes nonempty states. -/
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
namespace BayesCorrelated
universe uI uΘ uA uT uE
variable {I : Type uI} {Θ : Type uΘ} {A : I → Type uA} {T : I → Type uT}
variable [Fintype I] [DecidableEq I] [Fintype Θ]
variable [∀ i, Fintype (A i)] [∀ i, DecidableEq (A i)]
variable [∀ i, Fintype (T i)] [∀ i, DecidableEq (T i)]
variable {E : I → Type uE} [∀ i, Fintype (E i)] [∀ i, DecidableEq (E i)]

theorem finite_characterization (ψ : Θ → ℝ) (π : Θ → (∀ i, T i) → ℝ)
    (u : I → (∀ i, A i) → Θ → ℝ) (σ : Θ → (∀ i, T i) → (∀ i, A i) → ℝ)
    (_hψ : IsProbability ψ) (hπ : IsInformation π) (hσ : IsDecisionRule σ) :
    BCE ψ π u σ ↔ Implementable ψ π u σ := by
  sorry

theorem mixedBNE_induces_BCE (ψ : Θ → ℝ) (π : Θ → (∀ i, T i) → ℝ)
    (u : I → (∀ i, A i) → Θ → ℝ) (σ : Θ → (∀ i, T i) → (∀ i, A i) → ℝ)
    (q : Θ → (∀ i, T i) → (∀ i, E i) → ℝ)
    (β : ∀ i, T i → E i → A i → ℝ)
    (hβ : IsStrategy β) (hB : MixedBNE ψ u q β) (hi : Induces π σ q β) : BCE ψ π u σ := by
  sorry

end BayesCorrelated
namespace BayesCorrelated
universe uI uΘ uA uT uE
variable {I : Type uI} {Θ : Type uΘ} {A : I → Type uA} {T : I → Type uT}
variable [Fintype I] [DecidableEq I] [Fintype Θ]
variable [∀ i, Fintype (A i)] [∀ i, DecidableEq (A i)]
variable [∀ i, Fintype (T i)] [∀ i, DecidableEq (T i)]
variable {E : I → Type uE} [∀ i, Fintype (E i)] [∀ i, DecidableEq (E i)]

theorem expansion_normalized (π : Θ → (∀ i, T i) → ℝ)
    (q : Θ → (∀ i, T i) → (∀ i, E i) → ℝ)
    (hπ : IsInformation π) (hq : IsExpansion π q) (θ : Θ) :
    ∑ t, ∑ e, q θ t e = 1 := by
  sorry

theorem expansion_null_fiber (π : Θ → (∀ i, T i) → ℝ)
    (q : Θ → (∀ i, T i) → (∀ i, E i) → ℝ)
    (hq : IsExpansion π q) (θ : Θ) (t : ∀ i, T i) (h : π θ t = 0) (e : ∀ i, E i) :
    q θ t e = 0 := by
  sorry

theorem strategyProduct_isProbability (β : ∀ i, T i → E i → A i → ℝ)
    (hβ : IsStrategy β) (t : ∀ i, T i) (e : ∀ i, E i) :
    IsProbability (strategyProduct β t e) := by
  sorry

theorem induces_iff_positive_support (π : Θ → (∀ i, T i) → ℝ)
    (σ : Θ → (∀ i, T i) → (∀ i, A i) → ℝ)
    (q : Θ → (∀ i, T i) → (∀ i, E i) → ℝ)
    (β : ∀ i, T i → E i → A i → ℝ)
    (hπ : IsInformation π) (hq : IsExpansion π q) :
    Induces π σ q β ↔ ∀ θ t a, 0 < π θ t →
      (∑ e, q θ t e * strategyProduct β t e a) / π θ t = σ θ t a := by
  sorry

end BayesCorrelated
namespace BayesCorrelated
variable {Θ C S : Type*} [Fintype Θ] [Fintype C] [DecidableEq C] [Fintype S] [DecidableEq S]

theorem onePlayer_obedienceGain (ψ : Θ → ℝ) (π : Θ → S → ℝ)
    (u : C → Θ → ℝ) (σ : Θ → S → C → ℝ) (s : S) (x y : C) :
    obedienceGain (I := Unit) (A := fun _ => C) (T := fun _ => S)
      ψ (fun θ t => π θ (t ())) (fun _ a θ => u (a ()) θ)
      (fun θ t a => σ θ (t ()) (a ())) () s x y =
      ∑ θ, ψ θ * π θ s * σ θ s x * (u x θ - u y θ) := by
  sorry

theorem onePlayer_characterization (ψ : Θ → ℝ) (π : Θ → S → ℝ)
    (u : C → Θ → ℝ) (σ : Θ → S → C → ℝ)
    (hψ : IsProbability ψ) (hπ : ∀ θ, IsProbability (π θ))
    (hσ : ∀ θ s, IsProbability (σ θ s)) :
    (∀ s x y, 0 ≤ ∑ θ, ψ θ * π θ s * σ θ s x * (u x θ - u y θ)) ↔
      Implementable (I := Unit) (A := fun _ => C) (T := fun _ => S)
        ψ (fun θ t => π θ (t ())) (fun _ a θ => u (a ()) θ)
        (fun θ t a => σ θ (t ()) (a ())) := by
  sorry

end BayesCorrelated

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

namespace BayesCorrelated

/-- One-player stochastic garbling: the channel is independent of the state. -/
def IsGarbling {Θ S Z : Type*} [Fintype S] [Fintype Z]
    (π : Θ → S → ℝ) (ρ : Θ → Z → ℝ) : Prop :=
  ∃ k : S → Z → ℝ, (∀ s, IsProbability (k s)) ∧
    ∀ θ z, ρ θ z = ∑ s, π θ s * k s z

end BayesCorrelated

namespace BayesCorrelated
universe uI uΘ uT uE
variable {I : Type uI} {Θ : Type uΘ} {T : I → Type uT} {E : I → Type uE}
variable [Fintype I] [DecidableEq I] [Fintype Θ] [Nonempty Θ]
variable [∀ i, Fintype (T i)] [∀ i, DecidableEq (T i)]
variable [∀ i, Fintype (E i)] [∀ i, DecidableEq (E i)]

theorem information_order_characterization
    (π : Θ → (∀ i, T i) → ℝ) (ρ : Θ → (∀ i, E i) → ℝ)
    (hπ : IsInformation π) (hρ : IsInformation ρ) :
    IndividuallySufficient π ρ ↔ MoreIncentiveConstrained π ρ := by
  sorry

end BayesCorrelated
namespace BayesCorrelated
universe uI uΘ uA uT uE
variable {I : Type uI} {Θ : Type uΘ} {A : I → Type uA}
variable {T : I → Type uT} {E : I → Type uE}
variable [Fintype I] [DecidableEq I] [Fintype Θ]
variable [∀ i, Fintype (A i)] [∀ i, DecidableEq (A i)]
variable [∀ i, Fintype (T i)] [∀ i, DecidableEq (T i)]
variable [∀ i, Fintype (E i)] [∀ i, DecidableEq (E i)]

theorem individuallySufficient_outcome [Nonempty Θ]
    (ψ : Θ → ℝ) (π : Θ → (∀ i, T i) → ℝ) (ρ : Θ → (∀ i, E i) → ℝ)
    (hπ : IsInformation π) (hρ : IsInformation ρ)
    (hs : IndividuallySufficient π ρ)
    (u : I → (∀ i, A i) → Θ → ℝ) (ν : Θ → (∀ i, A i) → ℝ)
    (hv : IsBCEOutcome ψ π u ν) : IsBCEOutcome ψ ρ u ν := by
  sorry

end BayesCorrelated
namespace BayesCorrelated
universe uI uΘ uT uA uB uE
variable {I : Type uI} {Θ : Type uΘ} {T : I → Type uT}
variable {A : I → Type uA} {B : I → Type uB}
variable [Fintype I] [DecidableEq I] [Fintype Θ]
variable [∀ i, Fintype (T i)] [∀ i, DecidableEq (T i)]
variable [∀ i, Fintype (A i)] [∀ i, DecidableEq (A i)]
variable [∀ i, Fintype (B i)] [∀ i, DecidableEq (B i)]

theorem moreIncentiveConstrained_outcome_any_universe
    {E : I → Type uE} [∀ i, Fintype (E i)] [∀ i, DecidableEq (E i)]
    (ψ : Θ → ℝ) (π : Θ → (∀ i, T i) → ℝ) (ρ : Θ → (∀ i, E i) → ℝ)
    (ho : MoreIncentiveConstrained π ρ) (hψ : FullSupportPrior ψ)
    (u : I → (∀ i, A i) → Θ → ℝ) (ν : Θ → (∀ i, A i) → ℝ)
    (hv : IsBCEOutcome ψ π u ν) : IsBCEOutcome ψ ρ u ν := by
  sorry

end BayesCorrelated
namespace BayesCorrelated
variable {Θ S Z : Type*} [Fintype Θ] [Fintype S] [DecidableEq S]
variable [Fintype Z] [DecidableEq Z]

theorem onePlayer_individual_sufficiency (π : Θ → S → ℝ) (ρ : Θ → Z → ℝ)
    (hπ : ∀ θ, IsProbability (π θ)) :
    IndividuallySufficient (I := Unit) (T := fun _ => S) (E := fun _ => Z)
      (fun θ t => π θ (t ())) (fun θ e => ρ θ (e ())) ↔ IsGarbling π ρ := by
  sorry

end BayesCorrelated
namespace BayesCorrelated
variable {Θ S Z : Type*} [Fintype Θ] [Fintype S] [DecidableEq S]
variable [Fintype Z] [DecidableEq Z]

theorem onePlayer_information_order [Nonempty Θ] (π : Θ → S → ℝ) (ρ : Θ → Z → ℝ)
    (hπ : ∀ θ, IsProbability (π θ)) (hρ : ∀ θ, IsProbability (ρ θ)) :
    IsGarbling π ρ ↔ MoreIncentiveConstrained (I := Unit) (T := fun _ => S) (E := fun _ => Z)
      (fun θ t => π θ (t ())) (fun θ e => ρ θ (e ())) := by
  sorry

end BayesCorrelated
