module
public import BCE.ScoringExtraction
public import BCE.OrderMass

@[expose] public section
open scoped BigOperators
namespace BayesCorrelated.OrderImplementation
open BayesCorrelated
universe uI uΘ uT uE
variable {I : Type uI} {Θ : Type uΘ} {T : I → Type uT} {E : I → Type uE}
variable [Fintype I] [DecidableEq I] [Fintype Θ]
variable [∀ i, Fintype (T i)] [∀ i, DecidableEq (T i)]
variable [∀ i, Fintype (E i)] [∀ i, DecidableEq (E i)]

theorem scoring_residual_bound (ψ : Θ → ℝ) (π : Θ → (∀ i, T i) → ℝ)
    (ρ : Θ → (∀ i, E i) → ℝ) (δ : ℝ)
    (σ : Θ → (∀ i, E i) → (∀ i, TestAction (Θ := Θ) (T := T) i) → ℝ)
    (hψ : IsProbability ψ) (hπ : IsInformation π) (hρ : IsInformation ρ)
    (hσ : IsDecisionRule σ) (he : outcome ρ σ = outcome π truthfulRule)
    (hb : BCE ψ ρ (testUtility ψ π δ) σ) (hδ : 0 < δ)
    (i : I) (θ : Θ) (t : ∀ i, T i) (z : E i) :
    |independenceResidual ψ π (ruleCombination ρ σ) i θ t z| ≤ δ := by
  classical
  let q := ruleCombination ρ σ
  let s := t i
  let c : ScoreCoordinate (Θ := Θ) (T := T) i := (θ, fun j => t j.1)
  let r := coupledScoreMass ψ q i s z
  let p := originalBelief ψ π i s
  let d := typePriorMass ψ π i s
  let M := coupledTypeMass ψ q i s z
  have hq := ruleCombination_valid π ρ σ hρ hσ he
  have hp : 0 ≤ ∑ k, r k * (quadraticScore p k - quadraticScore (coordinatePerturb p c δ) k) := by
    have hh := hb i z (Sum.inl s) (Sum.inr (s, c, true))
    rw [ruleCombination_scoring_gain ψ π ρ δ σ hρ hσ he] at hh
    simpa only [testReport, ite_true] using hh
  have hm : 0 ≤ ∑ k, r k * (quadraticScore p k - quadraticScore (coordinatePerturb p c (-δ)) k) := by
    have hh := hb i z (Sum.inl s) (Sum.inr (s, c, false))
    rw [ruleCombination_scoring_gain ψ π ρ δ σ hρ hσ he] at hh
    simpa only [testReport, Bool.false_eq_true, ite_false] using hh
  have htest := signed_tests_bound r p c δ hδ hp hm
  have hM : (∑ k, r k) = M := (coupledMass_eq ψ q i s z).symm
  rw [hM] at htest
  have hd₀ : 0 ≤ d := typePriorMass_nonneg ψ π hψ hπ i s
  have hd₁ : d ≤ 1 := typePriorMass_le_one ψ π hψ hπ i s
  have hM₀ : 0 ≤ M := coupledTypeMass_nonneg ψ π ρ q hψ hq i s z
  have hM₁ : M ≤ 1 := coupledTypeMass_le_one ψ π ρ q hψ hπ hq i s z
  have hprod : d * M ≤ 1 := by
    simpa using mul_le_mul hd₁ hM₁ hM₀ zero_le_one
  have hcell : r c = coupledCellMass ψ q i θ t z := by
    change ψ θ * (∑ e, if e i = z then q θ ((Equiv.piSplitAt i T).symm ((Equiv.piSplitAt i T) t)) e else 0) = _
    rw [Equiv.symm_apply_apply]; rfl
  have hbase : originalMass ψ π i s c = ψ θ * π θ t := by
    change ψ θ * π θ ((Equiv.piSplitAt i T).symm ((Equiv.piSplitAt i T) t)) = _
    rw [Equiv.symm_apply_apply]
  have hdp : d * p c = ψ θ * π θ t := by
    rw [← hbase]
    change typePriorMass ψ π i s * originalBelief ψ π i s c = _
    rw [priorMass_eq]
    exact mass_div_identity (originalMass ψ π i s)
      (fun k => mul_nonneg (hψ.1 k.1) ((hπ k.1).1 _)) c
  have hR : independenceResidual ψ π q i θ t z = d * (r c - M * p c) := by
    change d * coupledCellMass ψ q i θ t z - M * (ψ θ * π θ t) = _
    rw [← hcell, ← hdp]; ring
  rw [hR, abs_mul, abs_of_nonneg hd₀]
  calc
    d * |r c - M * p c| ≤ d * (M * δ / 2) := mul_le_mul_of_nonneg_left htest hd₀
    _ ≤ δ := by nlinarith [mul_le_mul_of_nonneg_right hprod hδ.le]

theorem approximate_couplings_of_order (ψ : Θ → ℝ) (π : Θ → (∀ i, T i) → ℝ)
    (ρ : Θ → (∀ i, E i) → ℝ) (hψ : FullSupportPrior ψ)
    (hπ : IsInformation π) (hρ : IsInformation ρ) (ho : MoreIncentiveConstrained π ρ)
    (ε : ℝ) (hε : 0 < ε) : ∃ q, IsCombination π ρ q ∧
      ∀ i θ t z, |independenceResidual ψ π q i θ t z| ≤ ε := by
  obtain ⟨σ, hσ, hb, he, hq⟩ := scoring_game_transfer ψ π ρ ε hψ hπ hρ ho
  exact ⟨ruleCombination ρ σ, hq, scoring_residual_bound ψ π ρ ε σ hψ.1 hπ hρ hσ he hb hε⟩

end BayesCorrelated.OrderImplementation
