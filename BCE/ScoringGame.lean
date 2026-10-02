module
public import BCE.ScoringCore
public import BCE.OrderTransport
public import Mathlib.Logic.Equiv.Prod
public import Mathlib.Data.Fintype.BigOperators

@[expose] public section
open scoped BigOperators
namespace BayesCorrelated.OrderImplementation
open BayesCorrelated
universe uI uΘ uT
variable {I : Type uI} {Θ : Type uΘ} {T : I → Type uT}
variable [Fintype I] [DecidableEq I] [Fintype Θ]
variable [∀ i, Fintype (T i)] [∀ i, DecidableEq (T i)]

@[reducible] def OpponentTypes (i : I) := ∀ j : {j : I // j ≠ i}, T j
@[reducible] def ScoreCoordinate (i : I) := Θ × OpponentTypes (T := T) i
@[reducible] def TestAction (i : I) := T i ⊕ (T i × ScoreCoordinate (Θ := Θ) (T := T) i × Bool)

instance opponentTypesFintype (i : I) : Fintype (OpponentTypes (T := T) i) := inferInstanceAs (Fintype (∀ j : {j : I // j ≠ i}, T j))
instance opponentTypesDecidableEq (i : I) : DecidableEq (OpponentTypes (T := T) i) := inferInstanceAs (DecidableEq (∀ j : {j : I // j ≠ i}, T j))
instance scoreCoordinateFintype (i : I) : Fintype (ScoreCoordinate (Θ := Θ) (T := T) i) := inferInstanceAs (Fintype (Θ × OpponentTypes (T := T) i))
instance testActionFintype (i : I) : Fintype (TestAction (Θ := Θ) (T := T) i) := inferInstanceAs (Fintype (T i ⊕ (T i × ScoreCoordinate (Θ := Θ) (T := T) i × Bool)))
noncomputable instance testActionDecidableEq (i : I) : DecidableEq (TestAction (Θ := Θ) (T := T) i) := Classical.decEq _

noncomputable def originalMass (ψ : Θ → ℝ) (π : Θ → (∀ i, T i) → ℝ)
    (i : I) (s : T i) (c : ScoreCoordinate (Θ := Θ) (T := T) i) : ℝ :=
  ψ c.1 * π c.1 ((Equiv.piSplitAt i T).symm (s, c.2))

noncomputable def originalTypeMass (ψ : Θ → ℝ) (π : Θ → (∀ i, T i) → ℝ)
    (i : I) (s : T i) : ℝ := ∑ c, originalMass ψ π i s c

noncomputable def originalBelief (ψ : Θ → ℝ) (π : Θ → (∀ i, T i) → ℝ)
    (i : I) (s : T i) (c : ScoreCoordinate (Θ := Θ) (T := T) i) : ℝ :=
  originalMass ψ π i s c / originalTypeMass ψ π i s

noncomputable def testReport (ψ : Θ → ℝ) (π : Θ → (∀ i, T i) → ℝ)
    (δ : ℝ) (i : I) (a : TestAction (Θ := Θ) (T := T) i) :
    ScoreCoordinate (Θ := Θ) (T := T) i → ℝ := by
  classical
  exact match a with
    | Sum.inl s => originalBelief ψ π i s
    | Sum.inr (s, c, b) => coordinatePerturb (originalBelief ψ π i s) c (if b then δ else -δ)

def reportType (i : I) : TestAction (Θ := Θ) (T := T) i → T i
  | Sum.inl s => s
  | Sum.inr (s, _, _) => s

def embedTypes (t : ∀ i, T i) : ∀ i, TestAction (Θ := Θ) (T := T) i := fun i => Sum.inl (t i)

noncomputable def testUtility (ψ : Θ → ℝ) (π : Θ → (∀ i, T i) → ℝ) (δ : ℝ)
    (i : I) (a : ∀ i, TestAction (Θ := Θ) (T := T) i) (θ : Θ) : ℝ := by
  classical
  exact if ∀ j : {j : I // j ≠ i}, ∃ s, a j = Sum.inl s then
    quadraticScore (testReport ψ π δ i (a i)) (θ, fun j => reportType j.1 (a j.1)) else 0

noncomputable def truthfulRule (θ : Θ) (t : ∀ i, T i)
    (a : ∀ i, TestAction (Θ := Θ) (T := T) i) : ℝ := by
  classical
  exact if a = embedTypes t then 1 else 0

theorem truthfulRule_valid : IsDecisionRule (truthfulRule (Θ := Θ) (T := T)) := by
  classical
  intro θ t
  constructor
  · intro a; simp only [truthfulRule]; split_ifs <;> norm_num
  · simp [truthfulRule]

theorem embedTypes_injective : Function.Injective (embedTypes (Θ := Θ) (T := T)) := by
  intro t s h
  funext i
  exact Sum.inl.inj (congr_fun h i)

theorem testUtility_update (ψ : Θ → ℝ) (π : Θ → (∀ i, T i) → ℝ) (δ : ℝ)
    (i : I) (t : ∀ i, T i) (a : TestAction (Θ := Θ) (T := T) i) (θ : Θ) :
    testUtility ψ π δ i (Function.update (embedTypes t) i a) θ =
      quadraticScore (testReport ψ π δ i a) (θ, fun j : {j : I // j ≠ i} => t j) := by
  classical
  have h (j : {j : I // j ≠ i}) : Function.update (embedTypes (Θ := Θ) t) i a j = embedTypes t j := by
    exact Function.update_of_ne j.2 _ _
  have hg : ∀ j : {j : I // j ≠ i}, ∃ s, Function.update (embedTypes (Θ := Θ) t) i a j = Sum.inl s := by
    intro j; exact ⟨t j, h j⟩
  unfold testUtility
  rw [if_pos hg]
  simp only [Function.update_self, h, embedTypes, reportType]

theorem testUtility_embed (ψ : Θ → ℝ) (π : Θ → (∀ i, T i) → ℝ) (δ : ℝ)
    (i : I) (t : ∀ i, T i) (θ : Θ) :
    testUtility ψ π δ i (embedTypes t) θ =
      quadraticScore (originalBelief ψ π i (t i)) (θ, fun j : {j : I // j ≠ i} => t j) := by
  classical
  have hg : ∀ j : {j : I // j ≠ i}, ∃ s, embedTypes (Θ := Θ) t j = Sum.inl s := by
    intro j; exact ⟨t j, rfl⟩
  unfold testUtility
  rw [if_pos hg]
  simp only [embedTypes, reportType, testReport]

theorem sum_own_type (ψ : Θ → ℝ) (π : Θ → (∀ i, T i) → ℝ)
    (i : I) (s : T i) (f : ScoreCoordinate (Θ := Θ) (T := T) i → ℝ) :
    (∑ θ, ∑ t, if t i = s then ψ θ * π θ t * f (θ, fun j => t j.1) else 0) =
      ∑ c, originalMass ψ π i s c * f c := by
  classical
  have own (s' : T i) (r : OpponentTypes (T := T) i) :
      (Equiv.piSplitAt i T).symm (s', r) i = s' :=
    congrArg Prod.fst ((Equiv.piSplitAt i T).apply_symm_apply (s', r))
  have opp (s' : T i) (r : OpponentTypes (T := T) i) :
      (fun j : {j : I // j ≠ i} => (Equiv.piSplitAt i T).symm (s', r) j.1) = r :=
    congrArg Prod.snd ((Equiv.piSplitAt i T).apply_symm_apply (s', r))
  change _ = ∑ c : Θ × OpponentTypes (T := T) i, _
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl; intro θ _
  rw [← (Equiv.piSplitAt i T).symm.sum_comp
    (fun t => if t i = s then ψ θ * π θ t * f (θ, fun j => t j.1) else 0)]
  rw [Fintype.sum_prod_type]
  simp only [own, opp]
  simp [← Finset.ite_sum_zero, originalMass]

theorem truthful_gain (ψ : Θ → ℝ) (π : Θ → (∀ i, T i) → ℝ) (δ : ℝ)
    (i : I) (s : T i) (y : TestAction (Θ := Θ) (T := T) i) :
    obedienceGain ψ π (testUtility ψ π δ) truthfulRule i (s : T i) (Sum.inl s) y =
      ∑ c, originalMass ψ π i s c *
        (quadraticScore (originalBelief ψ π i s) c - quadraticScore (testReport ψ π δ i y) c) := by
  classical
  unfold obedienceGain
  have term (θ : Θ) (t : ∀ i, T i) :
      (∑ a, if t i = s ∧ a i = Sum.inl s then
        ψ θ * π θ t * truthfulRule θ t a *
          (testUtility ψ π δ i a θ - testUtility ψ π δ i (Function.update a i y) θ) else 0) =
      if t i = s then ψ θ * π θ t *
        (quadraticScore (originalBelief ψ π i s) (θ, fun j => t j.1) -
          quadraticScore (testReport ψ π δ i y) (θ, fun j => t j.1)) else 0 := by
    simp only [truthfulRule, mul_ite, mul_one, mul_zero, ite_mul, zero_mul]
    simp only [← ite_and]
    have hh (a : ∀ i, TestAction (Θ := Θ) (T := T) i) :
        (t i = s ∧ a i = Sum.inl s) ∧ a = embedTypes t ↔ a = embedTypes t ∧ t i = s := by
      constructor
      · rintro ⟨⟨ht, _⟩, ha⟩; exact ⟨ha, ht⟩
      · rintro ⟨rfl, ht⟩; simp [embedTypes, ht]
    simp only [hh]
    simp only [ite_and, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    rw [testUtility_embed, testUtility_update]
    by_cases ht : t i = s <;> simp [ht]
  simp_rw [term]
  exact sum_own_type ψ π i s (fun c =>
    quadraticScore (originalBelief ψ π i s) c - quadraticScore (testReport ψ π δ i y) c)

theorem truthful_gain_zero (ψ : Θ → ℝ) (π : Θ → (∀ i, T i) → ℝ) (δ : ℝ)
    (i : I) (s : T i) (x y : TestAction (Θ := Θ) (T := T) i)
    (h : x ≠ Sum.inl s) : obedienceGain ψ π (testUtility ψ π δ) truthfulRule i s x y = 0 := by
  classical
  unfold obedienceGain
  apply Finset.sum_eq_zero; intro θ _
  apply Finset.sum_eq_zero; intro t _
  apply Finset.sum_eq_zero; intro a _
  by_cases ha : a = embedTypes t
  · subst a
    have hx : ¬(t i = s ∧ embedTypes (Θ := Θ) t i = x) := by
      rintro ⟨ht, he⟩
      apply h
      exact he.symm.trans (congrArg Sum.inl ht)
    simp only [hx, ite_false]
  · simp [truthfulRule, ha]

theorem truthful_BCE (ψ : Θ → ℝ) (π : Θ → (∀ i, T i) → ℝ) (δ : ℝ)
    (hψ : IsProbability ψ) (hπ : IsInformation π) :
    BCE ψ π (testUtility ψ π δ) truthfulRule := by
  classical
  intro i s x y
  cases x with
  | inl r =>
    by_cases hs : s = r
    · subst r
      rw [truthful_gain]
      have hm (c : ScoreCoordinate (Θ := Θ) (T := T) i) : 0 ≤ originalMass ψ π i s c :=
        mul_nonneg (hψ.1 c.1) ((hπ c.1).1 _)
      apply weighted_score_gap_nonneg _ _ _ (originalTypeMass ψ π i s) rfl
      · intro c
        exact (mass_div_identity (originalMass ψ π i s) hm c).symm
      · exact Finset.sum_nonneg fun c _ => hm c
    · rw [truthful_gain_zero ψ π δ i s (Sum.inl r) y (by simpa using Ne.symm hs)]
  | inr r =>
    rw [truthful_gain_zero ψ π δ i s (Sum.inr r) y (by simp)]

end BayesCorrelated.OrderImplementation
