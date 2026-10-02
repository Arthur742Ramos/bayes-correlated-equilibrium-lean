module
public import BCE.InformationOrder

@[expose] public section
open scoped BigOperators
namespace BayesCorrelated

/-- One-player stochastic garbling: the channel is independent of the state. -/
def IsGarbling {Θ S Z : Type*} [Fintype S] [Fintype Z]
    (π : Θ → S → ℝ) (ρ : Θ → Z → ℝ) : Prop :=
  ∃ k : S → Z → ℝ, (∀ s, IsProbability (k s)) ∧
    ∀ θ z, ρ θ z = ∑ s, π θ s * k s z

end BayesCorrelated

namespace BayesCorrelated.OrderImplementation
open BayesCorrelated
variable {Θ S Z : Type*} [Fintype Θ] [Fintype S] [DecidableEq S]
variable [Fintype Z] [DecidableEq Z]

theorem lift_information (π : Θ → S → ℝ) (hπ : ∀ θ, IsProbability (π θ)) :
    IsInformation (T := fun _ : Unit => S) (fun θ t => π θ (t ())) := by
  intro θ
  constructor
  · intro t; exact (hπ θ).1 _
  · rw [← (Equiv.funUnique Unit S).symm.sum_comp]
    simpa [Equiv.funUnique, Equiv.piUnique] using (hπ θ).2

/-- Individual sufficiency reduces exactly to a stochastic garbling for one player. -/
theorem onePlayer_individual_sufficiency (π : Θ → S → ℝ) (ρ : Θ → Z → ℝ)
    (hπ : ∀ θ, IsProbability (π θ)) :
    IndividuallySufficient (I := Unit) (T := fun _ => S) (E := fun _ => Z)
      (fun θ t => π θ (t ())) (fun θ e => ρ θ (e ())) ↔ IsGarbling π ρ := by
  constructor
  · rintro ⟨q, φ, hq, hφ⟩
    refine ⟨φ (), hφ.1 (), ?_⟩
    intro θ z
    have hc (t : Unit → S) : q θ t (fun _ => z) = π θ (t ()) * φ () (t ()) z := by
      have hh := hφ.2 () θ t z
      rw [← (Equiv.funUnique Unit Z).symm.sum_comp] at hh
      simp only [Equiv.funUnique, Equiv.piUnique] at hh
      rw [Finset.sum_eq_single z] at hh
      · have hu : (uniqueElim z : Unit → Z) = (fun _ => z) := by
          funext i; cases i; rfl
        change (if z = z then q θ t (uniqueElim z) else 0) = _ at hh
        rw [if_pos rfl, hu] at hh
        exact hh
      · intro b _ hb; simp [hb]
      · simp
    have hm := hq.2 θ (fun _ => z)
    simp_rw [hc] at hm
    rw [← (Equiv.funUnique Unit S).symm.sum_comp] at hm
    simpa [Equiv.funUnique, Equiv.piUnique] using hm.symm
  · rintro ⟨k, hk, he⟩
    let q := fun θ (t : Unit → S) (e : Unit → Z) => π θ (t ()) * k (t ()) (e ())
    refine ⟨q, (fun _ => k), ⟨⟨?_, ?_⟩, ?_⟩, ?_, ?_⟩
    · intro θ t e; exact mul_nonneg ((hπ θ).1 _) ((hk _).1 _)
    · intro θ t
      rw [← (Equiv.funUnique Unit Z).symm.sum_comp]
      change (∑ z, π θ (t ()) * k (t ()) z) = π θ (t ())
      rw [← Finset.mul_sum, (hk _).2, mul_one]
    · intro θ e
      rw [← (Equiv.funUnique Unit S).symm.sum_comp]
      exact (he θ (e ())).symm
    · intro i s; cases i; exact hk s
    · intro i θ t z; cases i
      rw [← (Equiv.funUnique Unit Z).symm.sum_comp]
      simp only [q, Equiv.funUnique, Equiv.piUnique]
      rw [Finset.sum_eq_single z]
      · simp
      · intro b _ hb; simp [hb]
      · simp

/-- One-player information order is precisely stochastic garbling, across all finite decision games. -/
theorem onePlayer_information_order [Nonempty Θ] (π : Θ → S → ℝ) (ρ : Θ → Z → ℝ)
    (hπ : ∀ θ, IsProbability (π θ)) (hρ : ∀ θ, IsProbability (ρ θ)) :
    IsGarbling π ρ ↔ MoreIncentiveConstrained (I := Unit) (T := fun _ => S) (E := fun _ => Z)
      (fun θ t => π θ (t ())) (fun θ e => ρ θ (e ())) := by
  rw [← onePlayer_individual_sufficiency π ρ hπ]
  exact information_order_characterization _ _ (lift_information π hπ) (lift_information ρ hρ)

end BayesCorrelated.OrderImplementation
