module
public import BCE.Implementation
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
@[expose] public section
open scoped BigOperators
namespace BayesCorrelated.Implementation
open BayesCorrelated
universe uI uΘ uA uT uE
variable {I : Type uI} {Θ : Type uΘ} {A : I → Type uA} {T : I → Type uT}
variable [Fintype I] [DecidableEq I] [Fintype Θ]
variable [∀ i, Fintype (A i)] [∀ i, DecidableEq (A i)]
variable [∀ i, Fintype (T i)] [∀ i, DecidableEq (T i)]
variable {E : I → Type uE} [∀ i, Fintype (E i)] [∀ i, DecidableEq (E i)]

/-- Marginal preservation entails a normalized expanded information structure. -/
theorem expansion_normalized (π : Θ → (∀ i, T i) → ℝ)
    (q : Θ → (∀ i, T i) → (∀ i, E i) → ℝ)
    (hπ : IsInformation π) (hq : IsExpansion π q) (θ : Θ) :
    ∑ t, ∑ e, q θ t e = 1 := by
  simp_rw [hq.2 θ]
  exact (hπ θ).2

/-- A zero original-signal fiber has identically zero expansion mass. -/
theorem expansion_null_fiber (π : Θ → (∀ i, T i) → ℝ)
    (q : Θ → (∀ i, T i) → (∀ i, E i) → ℝ)
    (hq : IsExpansion π q) (θ : Θ) (t : ∀ i, T i) (h : π θ t = 0) (e : ∀ i, E i) :
    q θ t e = 0 := by
  have hz : ∑ e, q θ t e = 0 := (hq.2 θ t).trans h
  exact (Finset.sum_eq_zero_iff_of_nonneg (fun e _ => hq.1 θ t e)).mp hz e (Finset.mem_univ e)

/-- Independent behavioral play defines an actual normalized distribution over action profiles. -/
theorem strategyProduct_isProbability (β : ∀ i, T i → E i → A i → ℝ)
    (hβ : IsStrategy β) (t : ∀ i, T i) (e : ∀ i, E i) :
    IsProbability (strategyProduct β t e) := by
  constructor
  · intro a; exact Finset.prod_nonneg fun i _ => (hβ i (t i) (e i)).1 (a i)
  · simp only [strategyProduct]
    rw [← Fintype.prod_sum]
    simp only [fun i => (hβ i (t i) (e i)).2, Finset.prod_const_one]

/-- Agreement with the paper's quotient on every positive original-signal fiber
is equivalent to joint-law induction, with no condition on the null fibers. -/
theorem induces_iff_positive_support (π : Θ → (∀ i, T i) → ℝ)
    (σ : Θ → (∀ i, T i) → (∀ i, A i) → ℝ)
    (q : Θ → (∀ i, T i) → (∀ i, E i) → ℝ)
    (β : ∀ i, T i → E i → A i → ℝ)
    (hπ : IsInformation π) (hq : IsExpansion π q) :
    Induces π σ q β ↔ ∀ θ t a, 0 < π θ t →
      (∑ e, q θ t e * strategyProduct β t e a) / π θ t = σ θ t a := by
  constructor
  · intro hi θ t a h
    rw [← hi θ t a, mul_div_cancel_left₀ _ (ne_of_gt h)]
  · intro h θ t a
    rcases eq_or_lt_of_le ((hπ θ).1 t) with hz | hp
    · have hz' : π θ t = 0 := hz.symm
      simp [hz', expansion_null_fiber π q hq θ t hz']
    · have he := (div_eq_iff (ne_of_gt hp)).mp (h θ t a hp)
      exact (mul_comm _ _).trans he.symm

/-- The other marginal is itself an information kernel, so q is a combination in the paper's sense. -/
theorem expansion_extra_information (π : Θ → (∀ i, T i) → ℝ)
    (q : Θ → (∀ i, T i) → (∀ i, E i) → ℝ)
    (hπ : IsInformation π) (hq : IsExpansion π q) :
    ∀ θ, IsProbability (fun e => ∑ t, q θ t e) := by
  intro θ
  constructor
  · intro e; exact Finset.sum_nonneg fun t _ => hq.1 θ t e
  · rw [Finset.sum_comm]
    exact expansion_normalized π q hπ hq θ
end BayesCorrelated.Implementation
