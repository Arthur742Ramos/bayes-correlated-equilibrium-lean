module
public import BCE

@[expose] public section
open scoped BigOperators
namespace BayesCorrelated
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
  exact Implementation.finite_characterization ψ π u σ _hψ hπ hσ

theorem mixedBNE_induces_BCE (ψ : Θ → ℝ) (π : Θ → (∀ i, T i) → ℝ)
    (u : I → (∀ i, A i) → Θ → ℝ) (σ : Θ → (∀ i, T i) → (∀ i, A i) → ℝ)
    (q : Θ → (∀ i, T i) → (∀ i, E i) → ℝ)
    (β : ∀ i, T i → E i → A i → ℝ)
    (hβ : IsStrategy β) (hB : MixedBNE ψ u q β) (hi : Induces π σ q β) : BCE ψ π u σ := by
  exact Implementation.mixedBNE_induces_BCE ψ π u σ q β hβ hB hi

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
  exact Implementation.expansion_normalized π q hπ hq θ

theorem expansion_null_fiber (π : Θ → (∀ i, T i) → ℝ)
    (q : Θ → (∀ i, T i) → (∀ i, E i) → ℝ)
    (hq : IsExpansion π q) (θ : Θ) (t : ∀ i, T i) (h : π θ t = 0) (e : ∀ i, E i) :
    q θ t e = 0 := by
  exact Implementation.expansion_null_fiber π q hq θ t h e

theorem strategyProduct_isProbability (β : ∀ i, T i → E i → A i → ℝ)
    (hβ : IsStrategy β) (t : ∀ i, T i) (e : ∀ i, E i) :
    IsProbability (strategyProduct β t e) := by
  exact Implementation.strategyProduct_isProbability β hβ t e

theorem induces_iff_positive_support (π : Θ → (∀ i, T i) → ℝ)
    (σ : Θ → (∀ i, T i) → (∀ i, A i) → ℝ)
    (q : Θ → (∀ i, T i) → (∀ i, E i) → ℝ)
    (β : ∀ i, T i → E i → A i → ℝ)
    (hπ : IsInformation π) (hq : IsExpansion π q) :
    Induces π σ q β ↔ ∀ θ t a, 0 < π θ t →
      (∑ e, q θ t e * strategyProduct β t e a) / π θ t = σ θ t a := by
  exact Implementation.induces_iff_positive_support π σ q β hπ hq

end BayesCorrelated
namespace BayesCorrelated
variable {Θ C S : Type*} [Fintype Θ] [Fintype C] [DecidableEq C] [Fintype S] [DecidableEq S]

theorem onePlayer_obedienceGain (ψ : Θ → ℝ) (π : Θ → S → ℝ)
    (u : C → Θ → ℝ) (σ : Θ → S → C → ℝ) (s : S) (x y : C) :
    obedienceGain (I := Unit) (A := fun _ => C) (T := fun _ => S)
      ψ (fun θ t => π θ (t ())) (fun _ a θ => u (a ()) θ)
      (fun θ t a => σ θ (t ()) (a ())) () s x y =
      ∑ θ, ψ θ * π θ s * σ θ s x * (u x θ - u y θ) := by
  exact Implementation.onePlayer_obedienceGain ψ π u σ s x y

theorem onePlayer_characterization (ψ : Θ → ℝ) (π : Θ → S → ℝ)
    (u : C → Θ → ℝ) (σ : Θ → S → C → ℝ)
    (hψ : IsProbability ψ) (hπ : ∀ θ, IsProbability (π θ))
    (hσ : ∀ θ s, IsProbability (σ θ s)) :
    (∀ s x y, 0 ≤ ∑ θ, ψ θ * π θ s * σ θ s x * (u x θ - u y θ)) ↔
      Implementable (I := Unit) (A := fun _ => C) (T := fun _ => S)
        ψ (fun θ t => π θ (t ())) (fun _ a θ => u (a ()) θ)
        (fun θ t a => σ θ (t ()) (a ())) := by
  exact Implementation.onePlayer_characterization ψ π u σ hψ hπ hσ

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
  exact OrderImplementation.information_order_characterization π ρ hπ hρ

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
  exact OrderImplementation.individuallySufficient_outcome ψ π ρ hπ hρ hs u ν hv

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
  exact OrderImplementation.moreIncentiveConstrained_outcome_any_universe ψ π ρ ho hψ u ν hv

end BayesCorrelated
namespace BayesCorrelated
variable {Θ S Z : Type*} [Fintype Θ] [Fintype S] [DecidableEq S]
variable [Fintype Z] [DecidableEq Z]

theorem onePlayer_individual_sufficiency (π : Θ → S → ℝ) (ρ : Θ → Z → ℝ)
    (hπ : ∀ θ, IsProbability (π θ)) :
    IndividuallySufficient (I := Unit) (T := fun _ => S) (E := fun _ => Z)
      (fun θ t => π θ (t ())) (fun θ e => ρ θ (e ())) ↔ IsGarbling π ρ := by
  exact OrderImplementation.onePlayer_individual_sufficiency π ρ hπ

end BayesCorrelated
namespace BayesCorrelated
variable {Θ S Z : Type*} [Fintype Θ] [Fintype S] [DecidableEq S]
variable [Fintype Z] [DecidableEq Z]

theorem onePlayer_information_order [Nonempty Θ] (π : Θ → S → ℝ) (ρ : Θ → Z → ℝ)
    (hπ : ∀ θ, IsProbability (π θ)) (hρ : ∀ θ, IsProbability (ρ θ)) :
    IsGarbling π ρ ↔ MoreIncentiveConstrained (I := Unit) (T := fun _ => S) (E := fun _ => Z)
      (fun θ t => π θ (t ())) (fun θ e => ρ θ (e ())) := by
  exact OrderImplementation.onePlayer_information_order π ρ hπ hρ

end BayesCorrelated
