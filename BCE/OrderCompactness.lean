module
public import BCE.OrderTransport
public import Mathlib.Analysis.Convex.StdSimplex
public import Mathlib.Topology.Order.Compact
public import Mathlib.Tactic.FunProp

@[expose] public section
open scoped BigOperators
namespace BayesCorrelated.OrderImplementation
open BayesCorrelated
universe uI uΘ uT uE
variable {I : Type uI} {Θ : Type uΘ} {T : I → Type uT} {E : I → Type uE}
variable [Fintype I] [DecidableEq I] [Fintype Θ]
variable [∀ i, Fintype (T i)] [∀ i, DecidableEq (T i)]
variable [∀ i, Fintype (E i)] [∀ i, DecidableEq (E i)]

noncomputable def typePriorMass (ψ : Θ → ℝ) (π : Θ → (∀ i, T i) → ℝ)
    (i : I) (s : T i) : ℝ := ∑ θ, ∑ t, if t i = s then ψ θ * π θ t else 0

noncomputable def coupledTypeMass (ψ : Θ → ℝ)
    (q : Θ → (∀ i, T i) → (∀ i, E i) → ℝ) (i : I) (s : T i) (z : E i) : ℝ :=
  ∑ θ, ∑ t, ∑ e, if t i = s ∧ e i = z then ψ θ * q θ t e else 0

noncomputable def coupledCellMass (ψ : Θ → ℝ)
    (q : Θ → (∀ i, T i) → (∀ i, E i) → ℝ)
    (i : I) (θ : Θ) (t : ∀ i, T i) (z : E i) : ℝ :=
  ψ θ * ∑ e, if e i = z then q θ t e else 0

/-- A continuous weighted equation, defined even when either conditioning event has zero mass. -/
noncomputable def independenceResidual (ψ : Θ → ℝ) (π : Θ → (∀ i, T i) → ℝ)
    (q : Θ → (∀ i, T i) → (∀ i, E i) → ℝ)
    (i : I) (θ : Θ) (t : ∀ i, T i) (z : E i) : ℝ :=
  typePriorMass ψ π i (t i) * coupledCellMass ψ q i θ t z -
    coupledTypeMass ψ q i (t i) z * (ψ θ * π θ t)

theorem combination_entry_le_one (π : Θ → (∀ i, T i) → ℝ)
    (ρ : Θ → (∀ i, E i) → ℝ) (q : Θ → (∀ i, T i) → (∀ i, E i) → ℝ)
    (hπ : IsInformation π) (hq : IsCombination π ρ q)
    (θ : Θ) (t : ∀ i, T i) (e : ∀ i, E i) : q θ t e ≤ 1 := by
  have h₁ : q θ t e ≤ π θ t := by
    rw [← hq.1.2 θ t]
    exact Finset.single_le_sum (fun e _ => hq.1.1 θ t e) (Finset.mem_univ e)
  have h₂ : π θ t ≤ 1 := by
    rw [← (hπ θ).2]
    exact Finset.single_le_sum (fun t _ => (hπ θ).1 t) (Finset.mem_univ t)
  exact h₁.trans h₂

theorem combination_isClosed (π : Θ → (∀ i, T i) → ℝ)
    (ρ : Θ → (∀ i, E i) → ℝ) :
    IsClosed {q : Θ → (∀ i, T i) → (∀ i, E i) → ℝ | IsCombination π ρ q} := by
  simp only [IsCombination, IsExpansion, Set.setOf_and, Set.setOf_forall]
  refine (IsClosed.inter ?_ ?_).inter ?_
  · apply isClosed_iInter; intro θ
    apply isClosed_iInter; intro t
    apply isClosed_iInter; intro e
    exact isClosed_le continuous_const (by fun_prop)
  · apply isClosed_iInter; intro θ
    apply isClosed_iInter; intro t
    exact isClosed_eq (by fun_prop) continuous_const
  · apply isClosed_iInter; intro θ
    apply isClosed_iInter; intro e
    exact isClosed_eq (by fun_prop) continuous_const

theorem combination_isCompact (π : Θ → (∀ i, T i) → ℝ)
    (ρ : Θ → (∀ i, E i) → ℝ) (hπ : IsInformation π) :
    IsCompact {q : Θ → (∀ i, T i) → (∀ i, E i) → ℝ | IsCombination π ρ q} := by
  apply IsCompact.of_isClosed_subset (s := Set.Icc 0 1) isCompact_Icc
    (combination_isClosed π ρ)
  intro q hq
  constructor
  · intro θ t e; exact hq.1.1 θ t e
  · intro θ t e; exact combination_entry_le_one π ρ q hπ hq θ t e

theorem independenceResidual_continuous (ψ : Θ → ℝ)
    (π : Θ → (∀ i, T i) → ℝ) (i : I) (θ : Θ) (t : ∀ i, T i) (z : E i) :
    Continuous (fun q : Θ → (∀ i, T i) → (∀ i, E i) → ℝ =>
      independenceResidual ψ π q i θ t z) := by
  have hc : Continuous (fun q : Θ → (∀ i, T i) → (∀ i, E i) → ℝ =>
      coupledCellMass ψ q i θ t z) := by
    unfold coupledCellMass
    apply Continuous.mul continuous_const
    apply continuous_finsetSum; intro e _
    split_ifs <;> fun_prop
  have hm : Continuous (fun q : Θ → (∀ i, T i) → (∀ i, E i) → ℝ =>
      coupledTypeMass ψ q i (t i) z) := by
    unfold coupledTypeMass
    apply continuous_finsetSum; intro θ _
    apply continuous_finsetSum; intro t' _
    apply continuous_finsetSum; intro e _
    split_ifs <;> fun_prop
  exact (continuous_const.mul hc).sub (hm.mul continuous_const)

theorem residualBound_isClosed (ψ : Θ → ℝ) (π : Θ → (∀ i, T i) → ℝ) (ε : ℝ) :
    IsClosed {q : Θ → (∀ i, T i) → (∀ i, E i) → ℝ |
      ∀ i θ t z, |independenceResidual ψ π q i θ t z| ≤ ε} := by
  simp only [Set.ofPred_forall]
  apply isClosed_iInter; intro i
  apply isClosed_iInter; intro θ
  apply isClosed_iInter; intro t
  apply isClosed_iInter; intro z
  exact isClosed_le (independenceResidual_continuous ψ π i θ t z).abs continuous_const

/-- Arbitrarily accurate actual couplings have an exact zero-residual coupling.
All compactness constraints are weighted equations; no posterior ratio is taken to a limit. -/
theorem exact_coupling_of_approximate (ψ : Θ → ℝ) (π : Θ → (∀ i, T i) → ℝ)
    (ρ : Θ → (∀ i, E i) → ℝ) (hπ : IsInformation π)
    (ha : ∀ ε : ℝ, 0 < ε → ∃ q, IsCombination π ρ q ∧
      ∀ i θ t z, |independenceResidual ψ π q i θ t z| ≤ ε) :
    ∃ q, IsCombination π ρ q ∧ ∀ i θ t z, independenceResidual ψ π q i θ t z = 0 := by
  let K : Set (Θ → (∀ i, T i) → (∀ i, E i) → ℝ) := {q | IsCombination π ρ q}
  let C (ε : {ε : ℝ // 0 < ε}) := K ∩ {q | ∀ i θ t z, |independenceResidual ψ π q i θ t z| ≤ ε.1}
  have hc (ε : {ε : ℝ // 0 < ε}) : IsClosed (C ε) :=
    (combination_isClosed π ρ).inter (residualBound_isClosed ψ π ε.1)
  have hk (ε : {ε : ℝ // 0 < ε}) : IsCompact (C ε) :=
    (combination_isCompact π ρ hπ).inter_right (residualBound_isClosed ψ π ε.1)
  have hn (ε : {ε : ℝ // 0 < ε}) : (C ε).Nonempty := ha ε.1 ε.2
  have hd : Directed (· ⊇ ·) C := by
    intro ε η
    refine ⟨⟨min ε.1 η.1, lt_min ε.2 η.2⟩, ?_, ?_⟩
    · intro q hq; exact ⟨hq.1, fun i θ t z => (hq.2 i θ t z).trans (min_le_left _ _)⟩
    · intro q hq; exact ⟨hq.1, fun i θ t z => (hq.2 i θ t z).trans (min_le_right _ _)⟩
  haveI : Nonempty {ε : ℝ // 0 < ε} := ⟨⟨1, zero_lt_one⟩⟩
  obtain ⟨q, hq⟩ := IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed C hd hn hk hc
  have hmem (ε : ℝ) (hε : 0 < ε) : q ∈ C ⟨ε, hε⟩ := Set.mem_iInter.mp hq _
  refine ⟨q, (hmem 1 zero_lt_one).1, ?_⟩
  intro i θ t z
  by_contra h
  have hp : 0 < |independenceResidual ψ π q i θ t z| := abs_pos.mpr h
  have hb := (hmem (|independenceResidual ψ π q i θ t z| / 2) (by linarith)).2 i θ t z
  linarith

end BayesCorrelated.OrderImplementation
