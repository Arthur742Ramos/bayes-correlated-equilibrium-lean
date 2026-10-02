module
public import BCE.OrderDefs
public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Linarith

@[expose] public section
open scoped BigOperators
namespace BayesCorrelated.OrderImplementation

variable {X : Type*} [Fintype X]

/-- Quadratic scoring accepts any real report vector; report vectors need not be probabilities. -/
noncomputable def quadraticScore (v : X → ℝ) (c : X) : ℝ :=
  2 * v c - ∑ k, (v k) ^ 2

theorem mass_div_identity (m : X → ℝ) (hm : ∀ c, 0 ≤ m c) (c : X) :
    (∑ k, m k) * (m c / ∑ k, m k) = m c := by
  by_cases h : ∑ k, m k = 0
  · have hc := (Finset.sum_eq_zero_iff_of_nonneg (fun k _ => hm k)).mp h c
      (Finset.mem_univ c)
    simp [h, hc]
  · exact mul_div_cancel₀ _ h

/-- Proper scoring, in weighted form, including the zero-mass case. -/
theorem weighted_score_gap (m p v : X → ℝ) (d : ℝ)
    (hd : ∑ c, m c = d) (hp : ∀ c, m c = d * p c) :
    (∑ c, m c * (quadraticScore p c - quadraticScore v c)) =
      d * ∑ c, (p c - v c) ^ 2 := by
  simp only [quadraticScore, sub_sub_sub_comm, mul_sub, Finset.sum_sub_distrib]
  simp_rw [← Finset.sum_mul, hd]
  simp_rw [hp, mul_assoc, ← Finset.mul_sum]
  simp_rw [show ∀ c, (p c - v c) ^ 2 =
    p c * (2 * p c) - p c * (2 * v c) - (p c) ^ 2 + (v c) ^ 2 by intro c; ring]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  ring

theorem weighted_score_gap_nonneg (m p v : X → ℝ) (d : ℝ)
    (hd : ∑ c, m c = d) (hp : ∀ c, m c = d * p c) (h : 0 ≤ d) :
    0 ≤ ∑ c, m c * (quadraticScore p c - quadraticScore v c) := by
  rw [weighted_score_gap m p v d hd hp]
  exact mul_nonneg h (Finset.sum_nonneg fun c _ => sq_nonneg _)

noncomputable def coordinatePerturb [DecidableEq X] (p : X → ℝ) (c : X) (h : ℝ) : X → ℝ :=
  fun k => p k + if k = c then h else 0

theorem perturb_square_sum [DecidableEq X] (p : X → ℝ) (c : X) (h : ℝ) :
    ∑ k, (coordinatePerturb p c h k) ^ 2 = (∑ k, (p k) ^ 2) + 2 * h * p c + h ^ 2 := by
  have ht (k : X) : (coordinatePerturb p c h k) ^ 2 =
      (p k) ^ 2 + if k = c then 2 * h * p c + h ^ 2 else 0 := by
    by_cases hk : k = c
    · subst k; simp only [coordinatePerturb, ite_true]; ring
    · simp [coordinatePerturb, hk]
  simp only [ht, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  ring

/-- Each signed coordinate report gives a linear test of one posterior-independence residual. -/
theorem weighted_score_perturb [DecidableEq X] (r p : X → ℝ) (c : X) (h : ℝ) :
    (∑ k, r k * (quadraticScore p k - quadraticScore (coordinatePerturb p c h) k)) =
      h ^ 2 * (∑ k, r k) - 2 * h * (r c - (∑ k, r k) * p c) := by
  have ht (k : X) : r k * (quadraticScore p k -
      quadraticScore (coordinatePerturb p c h) k) =
      r k * (2 * h * p c + h ^ 2) - if k = c then 2 * h * r c else 0 := by
    simp only [quadraticScore]
    rw [perturb_square_sum]
    simp only [coordinatePerturb]
    by_cases hk : k = c
    · subst k; simp only [ite_true]; ring
    · simp only [hk, ite_false]; ring
  simp only [ht, Finset.sum_sub_distrib, ← Finset.sum_mul,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  ring

theorem signed_tests_bound [DecidableEq X] (r p : X → ℝ) (c : X) (δ : ℝ)
    (hδ : 0 < δ)
    (hplus : 0 ≤ ∑ k, r k *
      (quadraticScore p k - quadraticScore (coordinatePerturb p c δ) k))
    (hminus : 0 ≤ ∑ k, r k *
      (quadraticScore p k - quadraticScore (coordinatePerturb p c (-δ)) k)) :
    |r c - (∑ k, r k) * p c| ≤ (∑ k, r k) * δ / 2 := by
  rw [weighted_score_perturb] at hplus hminus
  apply abs_le.mpr
  constructor
  · nlinarith
  · nlinarith

end BayesCorrelated.OrderImplementation
