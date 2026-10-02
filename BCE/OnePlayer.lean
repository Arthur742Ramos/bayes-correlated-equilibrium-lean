module
public import BCE.Support
@[expose] public section
open scoped BigOperators
namespace BayesCorrelated.Implementation
open BayesCorrelated
variable {Θ C S : Type*} [Fintype Θ] [Fintype C] [DecidableEq C] [Fintype S] [DecidableEq S]

/-- For one player the weighted obedience gain is precisely the decision-problem inequality. -/
theorem onePlayer_obedienceGain (ψ : Θ → ℝ) (π : Θ → S → ℝ)
    (u : C → Θ → ℝ) (σ : Θ → S → C → ℝ) (s : S) (x y : C) :
    obedienceGain (I := Unit) (A := fun _ => C) (T := fun _ => S)
      ψ (fun θ t => π θ (t ())) (fun _ a θ => u (a ()) θ)
      (fun θ t a => σ θ (t ()) (a ())) () s x y =
      ∑ θ, ψ θ * π θ s * σ θ s x * (u x θ - u y θ) := by
  simp only [obedienceGain]
  apply Finset.sum_congr rfl; intro θ _
  rw [← (Equiv.funUnique Unit S).symm.sum_comp]
  simp only [Equiv.funUnique, Equiv.piUnique]
  apply (show (∑ s', ∑ a : Unit → C, if s' = s ∧ a () = x then
    ψ θ * π θ s' * σ θ s' (a ()) * (u (a ()) θ - u y θ) else 0) = _ from ?_)
  · rw [Finset.sum_eq_single s]
    · rw [← (Equiv.funUnique Unit C).symm.sum_comp]
      simp [Equiv.funUnique, Equiv.piUnique]
    · intro b _ hbs; simp [hbs]
    · simp

/-- One-player specialization: an obedient decision rule is implemented by extra information. -/
theorem onePlayer_characterization (ψ : Θ → ℝ) (π : Θ → S → ℝ)
    (u : C → Θ → ℝ) (σ : Θ → S → C → ℝ)
    (hψ : IsProbability ψ) (hπ : ∀ θ, IsProbability (π θ))
    (hσ : ∀ θ s, IsProbability (σ θ s)) :
    (∀ s x y, 0 ≤ ∑ θ, ψ θ * π θ s * σ θ s x * (u x θ - u y θ)) ↔
      Implementable (I := Unit) (A := fun _ => C) (T := fun _ => S)
        ψ (fun θ t => π θ (t ())) (fun _ a θ => u (a ()) θ)
        (fun θ t a => σ θ (t ()) (a ())) := by
  have hp : IsInformation (T := fun _ : Unit => S) (fun θ t => π θ (t ())) := by
    intro θ
    constructor
    · intro t; exact (hπ θ).1 _
    · rw [← (Equiv.funUnique Unit S).symm.sum_comp]
      simpa [Equiv.funUnique, Equiv.piUnique] using (hπ θ).2
  have hs : IsDecisionRule (A := fun _ : Unit => C) (T := fun _ : Unit => S)
      (fun θ t a => σ θ (t ()) (a ())) := by
    intro θ t
    constructor
    · intro a; exact (hσ θ _).1 _
    · rw [← (Equiv.funUnique Unit C).symm.sum_comp]
      simpa [Equiv.funUnique, Equiv.piUnique] using (hσ θ (t ())).2
  rw [← finite_characterization _ _ _ _ hψ hp hs]
  constructor
  · intro h i s x y
    cases i
    rw [onePlayer_obedienceGain]
    exact h s x y
  · intro h s x y
    simpa only [onePlayer_obedienceGain] using h () s x y
end BayesCorrelated.Implementation
