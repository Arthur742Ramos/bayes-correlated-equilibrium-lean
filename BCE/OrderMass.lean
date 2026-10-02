module
public import BCE.OrderCompactness

@[expose] public section
open scoped BigOperators
namespace BayesCorrelated.OrderImplementation
open BayesCorrelated
universe uI uΘ uT uE
variable {I : Type uI} {Θ : Type uΘ} {T : I → Type uT} {E : I → Type uE}
variable [Fintype I] [DecidableEq I] [Fintype Θ]
variable [∀ i, Fintype (T i)] [∀ i, DecidableEq (T i)]
variable [∀ i, Fintype (E i)] [∀ i, DecidableEq (E i)]

theorem typePriorMass_nonneg (ψ : Θ → ℝ) (π : Θ → (∀ i, T i) → ℝ)
    (hψ : IsProbability ψ) (hπ : IsInformation π) (i : I) (s : T i) :
    0 ≤ typePriorMass ψ π i s := by
  apply Finset.sum_nonneg; intro θ _
  apply Finset.sum_nonneg; intro t _
  split_ifs
  · exact mul_nonneg (hψ.1 θ) ((hπ θ).1 t)
  · exact le_rfl

theorem typePriorMass_le_one (ψ : Θ → ℝ) (π : Θ → (∀ i, T i) → ℝ)
    (hψ : IsProbability ψ) (hπ : IsInformation π) (i : I) (s : T i) :
    typePriorMass ψ π i s ≤ 1 := by
  have hn : ∑ θ, ∑ t, ψ θ * π θ t = 1 := by
    simp_rw [← Finset.mul_sum, (hπ _).2, mul_one]
    exact hψ.2
  rw [← hn]
  apply Finset.sum_le_sum; intro θ _
  apply Finset.sum_le_sum; intro t _
  split_ifs
  · exact le_rfl
  · exact mul_nonneg (hψ.1 θ) ((hπ θ).1 t)

theorem coupledTypeMass_nonneg (ψ : Θ → ℝ) (π : Θ → (∀ i, T i) → ℝ)
    (ρ : Θ → (∀ i, E i) → ℝ) (q : Θ → (∀ i, T i) → (∀ i, E i) → ℝ)
    (hψ : IsProbability ψ) (hq : IsCombination π ρ q) (i : I) (s : T i) (z : E i) :
    0 ≤ coupledTypeMass ψ q i s z := by
  apply Finset.sum_nonneg; intro θ _
  apply Finset.sum_nonneg; intro t _
  apply Finset.sum_nonneg; intro e _
  split_ifs
  · exact mul_nonneg (hψ.1 θ) (hq.1.1 θ t e)
  · exact le_rfl

theorem coupledTypeMass_le_one (ψ : Θ → ℝ) (π : Θ → (∀ i, T i) → ℝ)
    (ρ : Θ → (∀ i, E i) → ℝ) (q : Θ → (∀ i, T i) → (∀ i, E i) → ℝ)
    (hψ : IsProbability ψ) (hπ : IsInformation π) (hq : IsCombination π ρ q)
    (i : I) (s : T i) (z : E i) : coupledTypeMass ψ q i s z ≤ 1 := by
  have hn : ∑ θ, ∑ t, ∑ e, ψ θ * q θ t e = 1 := by
    simp_rw [← Finset.mul_sum, hq.1.2, (hπ _).2, mul_one]
    exact hψ.2
  rw [← hn]
  apply Finset.sum_le_sum; intro θ _
  apply Finset.sum_le_sum; intro t _
  apply Finset.sum_le_sum; intro e _
  split_ifs
  · exact le_rfl
  · exact mul_nonneg (hψ.1 θ) (hq.1.1 θ t e)

theorem coupledTypeMass_sum (ψ : Θ → ℝ) (π : Θ → (∀ i, T i) → ℝ)
    (ρ : Θ → (∀ i, E i) → ℝ) (q : Θ → (∀ i, T i) → (∀ i, E i) → ℝ)
    (hq : IsCombination π ρ q) (i : I) (s : T i) :
    ∑ z, coupledTypeMass ψ q i s z = typePriorMass ψ π i s := by
  simp only [coupledTypeMass, typePriorMass]
  conv_lhs =>
    rw [Finset.sum_comm]
    arg 2; ext θ; rw [Finset.sum_comm]
    arg 2; ext t; rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro θ _
  apply Finset.sum_congr rfl; intro t _
  by_cases ht : t i = s
  · simp only [ht, true_and, ite_true]
    simp only [Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    rw [← Finset.mul_sum, hq.1.2]
  · simp [ht]

theorem null_type_row (ψ : Θ → ℝ) (π : Θ → (∀ i, T i) → ℝ)
    (hψ : FullSupportPrior ψ) (hπ : IsInformation π) (i : I) (s : T i)
    (hd : typePriorMass ψ π i s = 0) (θ : Θ) (t : ∀ i, T i) (ht : t i = s) :
    π θ t = 0 := by
  have hn (θ : Θ) (t : ∀ i, T i) :
      0 ≤ if t i = s then ψ θ * π θ t else 0 := by
    split_ifs
    · exact mul_nonneg (hψ.1.1 θ) ((hπ θ).1 t)
    · exact le_rfl
  have hθ := (Finset.sum_eq_zero_iff_of_nonneg
    (fun θ _ => Finset.sum_nonneg fun t _ => hn θ t)).mp hd θ (Finset.mem_univ θ)
  have hcell := (Finset.sum_eq_zero_iff_of_nonneg (fun t _ => hn θ t)).mp hθ t
    (Finset.mem_univ t)
  have hz : ψ θ * π θ t = 0 := by simpa only [ht, ite_true] using hcell
  exact (mul_eq_zero.mp hz).resolve_left (ne_of_gt (hψ.2 θ))

end BayesCorrelated.OrderImplementation
