module
public import BCE.ScoringApproximation

@[expose] public section
open scoped BigOperators
namespace BayesCorrelated.OrderImplementation
open BayesCorrelated
universe uI uΘ uT uE
variable {I : Type uI} {Θ : Type uΘ} {T : I → Type uT} {E : I → Type uE}
variable [Fintype I] [DecidableEq I] [Fintype Θ] [Nonempty Θ]
variable [∀ i, Fintype (T i)] [∀ i, DecidableEq (T i)]
variable [∀ i, Fintype (E i)] [∀ i, DecidableEq (E i)]

theorem individual_channels_of_zero_residual (ψ : Θ → ℝ)
    (π : Θ → (∀ i, T i) → ℝ) (ρ : Θ → (∀ i, E i) → ℝ)
    (q : Θ → (∀ i, T i) → (∀ i, E i) → ℝ) (hψ : FullSupportPrior ψ)
    (hπ : IsInformation π) (hρ : IsInformation ρ) (hq : IsCombination π ρ q)
    (hz : ∀ i θ t z, independenceResidual ψ π q i θ t z = 0) :
    ∃ φ, HasIndividualChannels π q φ := by
  classical
  let θ₀ : Θ := Classical.arbitrary Θ
  letI := probability_nonempty (ρ θ₀) (hρ θ₀)
  let e₀ : ∀ i, E i := Classical.arbitrary _
  let φ : ∀ i, T i → E i → ℝ := fun i s z =>
    if typePriorMass ψ π i s = 0 then (if z = e₀ i then 1 else 0)
    else coupledTypeMass ψ q i s z / typePriorMass ψ π i s
  refine ⟨φ, ?_, ?_⟩
  · intro i s
    by_cases hd : typePriorMass ψ π i s = 0
    · constructor
      · intro z; simp only [φ, hd, ite_true]; split_ifs <;> norm_num
      · simp [φ, hd]
    · constructor
      · intro z
        simp only [φ, hd, ite_false]
        exact div_nonneg (coupledTypeMass_nonneg ψ π ρ q hψ.1 hq i s z)
          (typePriorMass_nonneg ψ π hψ.1 hπ i s)
      · simp only [φ, hd, ite_false]
        rw [← Finset.sum_div, coupledTypeMass_sum ψ π ρ q hq, div_self hd]
  · intro i θ t z
    by_cases hd : typePriorMass ψ π i (t i) = 0
    · have hp := null_type_row ψ π hψ hπ i (t i) hd θ t rfl
      simp only [hp, zero_mul]
      have he (e : ∀ i, E i) := Implementation.expansion_null_fiber π q hq.1 θ t hp e
      simp [he]
    · have hr := sub_eq_zero.mp (hz i θ t z)
      have hc : typePriorMass ψ π i (t i) * (∑ e, if e i = z then q θ t e else 0) =
          coupledTypeMass ψ q i (t i) z * π θ t := by
        apply mul_left_cancel₀ (ne_of_gt (hψ.2 θ))
        calc
          ψ θ * (typePriorMass ψ π i (t i) * (∑ e, if e i = z then q θ t e else 0)) =
              typePriorMass ψ π i (t i) * coupledCellMass ψ q i θ t z := by
                unfold coupledCellMass; ring
          _ = coupledTypeMass ψ q i (t i) z * (ψ θ * π θ t) := hr
          _ = ψ θ * (coupledTypeMass ψ q i (t i) z * π θ t) := by ring
      simp only [φ, hd, ite_false]
      rw [← mul_div_assoc]
      apply (eq_div_iff hd).mpr
      calc
        (∑ e, if e i = z then q θ t e else 0) * typePriorMass ψ π i (t i) =
          typePriorMass ψ π i (t i) * (∑ e, if e i = z then q θ t e else 0) := mul_comm _ _
        _ = coupledTypeMass ψ q i (t i) z * π θ t := hc
        _ = π θ t * coupledTypeMass ψ q i (t i) z := mul_comm _ _

noncomputable def uniformPrior (θ : Θ) : ℝ := (Fintype.card Θ : ℝ)⁻¹

theorem uniformPrior_fullSupport : FullSupportPrior (uniformPrior (Θ := Θ)) := by
  have hc : 0 < (Fintype.card Θ : ℝ) := Nat.cast_pos.mpr Fintype.card_pos
  constructor
  · constructor
    · intro θ; exact inv_nonneg.mpr hc.le
    · simp [uniformPrior, Finset.sum_const, nsmul_eq_mul, ne_of_gt hc]
  · intro θ; exact inv_pos.mpr hc

/-- Converse for an actual all-games order, proved by finite scoring games and weighted compactness. -/
theorem moreIncentiveConstrained_individuallySufficient
    (π : Θ → (∀ i, T i) → ℝ) (ρ : Θ → (∀ i, E i) → ℝ)
    (hπ : IsInformation π) (hρ : IsInformation ρ) (ho : MoreIncentiveConstrained π ρ) :
    IndividuallySufficient π ρ := by
  let ψ := uniformPrior (Θ := Θ)
  have hψ : FullSupportPrior ψ := uniformPrior_fullSupport
  obtain ⟨q, hq, hz⟩ := exact_coupling_of_approximate ψ π ρ hπ
    (approximate_couplings_of_order ψ π ρ hψ hπ hρ ho)
  obtain ⟨φ, hφ⟩ := individual_channels_of_zero_residual ψ π ρ q hψ hπ hρ hq hz
  exact ⟨q, φ, hq, hφ⟩

/-- Bergemann–Morris Theorem 2 for arbitrary finite heterogeneous information structures.
The outcome order ranges over all finite basic games, with full-support common priors. -/
theorem information_order_characterization
    (π : Θ → (∀ i, T i) → ℝ) (ρ : Θ → (∀ i, E i) → ℝ)
    (hπ : IsInformation π) (hρ : IsInformation ρ) :
    IndividuallySufficient π ρ ↔ MoreIncentiveConstrained π ρ := by
  exact ⟨individuallySufficient_moreIncentiveConstrained π ρ hπ hρ,
    moreIncentiveConstrained_individuallySufficient π ρ hπ hρ⟩

end BayesCorrelated.OrderImplementation
