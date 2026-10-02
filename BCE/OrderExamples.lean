module
public import BCE.OnePlayerOrder

@[expose] public section
open scoped BigOperators
namespace BayesCorrelated.OrderExamples
open BayesCorrelated OrderImplementation

def revelation (θ s : Bool) : ℝ := if s = θ then 1 else 0
def redundantNull (_θ s : Bool) : ℝ := if s = false then 1 else 0

theorem revelation_valid (θ : Bool) : IsProbability (revelation θ) := by
  constructor
  · intro s; simp only [revelation]; split_ifs <;> norm_num
  · cases θ <;> norm_num [revelation, Fintype.sum_bool]

theorem redundantNull_valid (θ : Bool) : IsProbability (redundantNull θ) := by
  constructor
  · intro s; cases s <;> norm_num [redundantNull]
  · norm_num [redundantNull, Fintype.sum_bool]

/-- Perfect observation garbles to an uninformative experiment with an impossible signal. -/
theorem revelation_garbles_to_null : IsGarbling revelation redundantNull := by
  refine ⟨fun _ z => if z = false then 1 else 0, ?_, ?_⟩
  · intro s; exact redundantNull_valid s
  · intro θ z; cases θ <;> cases z <;> norm_num [revelation, redundantNull, Fintype.sum_bool]

theorem revelation_more_constrained :
    MoreIncentiveConstrained (I := Unit) (T := fun _ => Bool) (E := fun _ => Bool)
      (fun θ t => revelation θ (t ())) (fun θ e => redundantNull θ (e ())) :=
  (onePlayer_information_order revelation redundantNull revelation_valid redundantNull_valid).mp
    revelation_garbles_to_null

/-- The reverse order fails: an uninformative signal cannot stochastically reveal the state. -/
theorem null_cannot_garble_to_revelation : ¬ IsGarbling redundantNull revelation := by
  rintro ⟨k, _, he⟩
  have hf := he false true
  have ht := he true true
  norm_num [revelation, redundantNull, Fintype.sum_bool] at hf ht
  linarith

theorem null_not_more_constrained :
    ¬ MoreIncentiveConstrained (I := Unit) (T := fun _ => Bool) (E := fun _ => Bool)
      (fun θ t => redundantNull θ (t ())) (fun θ e => revelation θ (e ())) := by
  intro h
  exact null_cannot_garble_to_revelation
    ((onePlayer_information_order redundantNull revelation redundantNull_valid revelation_valid).mpr h)

noncomputable def correlatedSignals (_θ : Unit) (e : Bool → Bool) : ℝ :=
  if e false = e true then 1 / 2 else 0

theorem correlatedSignals_valid : IsInformation correlatedSignals := by
  intro θ
  constructor
  · intro e; simp only [correlatedSignals]; split_ifs <;> norm_num
  · rw [← (Equiv.boolArrowEquivProd Bool).symm.sum_comp]
    norm_num [correlatedSignals, Equiv.boolArrowEquivProd, Fintype.sum_prod_type, Fintype.sum_bool]

theorem correlatedSignals_marginal (θ : Unit) (i z : Bool) :
    (∑ e : Bool → Bool, if e i = z then correlatedSignals θ e else 0) = 1 / 2 := by
  rw [← (Equiv.boolArrowEquivProd Bool).symm.sum_comp]
  cases i <;> cases z <;>
    norm_num [correlatedSignals, Equiv.boolArrowEquivProd, Fintype.sum_prod_type, Fintype.sum_bool]

/-- A null experiment is individually sufficient for state-independent correlated signals.
The common coupling preserves correlation across the two players. -/
theorem null_sufficient_for_correlated_signals :
    IndividuallySufficient (T := fun _ : Bool => Unit) (fun _θ : Unit => fun _t => (1 : ℝ))
      correlatedSignals := by
  refine ⟨(fun θ _t e => correlatedSignals θ e), (fun _ _ _ => 1 / 2), ?_, ?_⟩
  · constructor
    · constructor
      · intro θ t e; exact (correlatedSignals_valid θ).1 e
      · intro θ t; exact (correlatedSignals_valid θ).2
    · intro θ e; simp
  · constructor
    · intro i s; constructor
      · intro z; norm_num
      · norm_num [Fintype.sum_bool]
    · intro i θ t z
      simpa only [one_mul] using correlatedSignals_marginal θ i z

theorem correlated_channel_is_not_product :
    correlatedSignals () (fun _ => false) ≠ (1 / 2 : ℝ) * (1 / 2 : ℝ) := by
  norm_num [correlatedSignals]

end BayesCorrelated.OrderExamples
