module
public import proofs.PhosphorylationStableCapacity.RateRegularOriginalMatrix
public import proofs.PhosphorylationStableCapacity.GeneralEquilibriumBudget

@[expose] public section

namespace PhosphorylationStableCapacity

open PhosphorylationSharpness

noncomputable section

/-- The exact finite regular-equilibrium input for the missing degree
argument: an arbitrarily nearby positive rate list has only regular
positive equilibria, and their total number is at most `2n`. -/
theorem nearby_positive_rates_finite_regular_budget {n : ℕ}
    (hn : 0 < n) (ET FT ST : ℝ) (hET : 0 < ET) (hFT : 0 < FT)
    (k : Rates n) (hk : k.Positive)
    {U : Set (CoordinateSpace n)} (hU : IsOpen U)
    (hzero : (0 : CoordinateSpace n) ∈ U) :
    ∃ v ∈ U, (ratesAdd k (selectedRates v)).Positive ∧
      let E : Set (State n) :=
        {x | x.Positive ∧
          Equilibrium (ratesAdd k (selectedRates v)) x ∧
          InClass ET FT ST x}
      E.Finite ∧ E.ncard ≤ 2*n ∧
        ∀ x ∈ E,
          (restrictedJacobianMatrix ET FT ST
            (ratesAdd k (selectedRates v))
            (toCoordinateSpace (chart x))).det ≠ 0 := by
  obtain ⟨v, hvU, hvpos, hvregular⟩ :=
    nearby_positive_rates_literal_equilibria_regular
      ET FT ST k hk hU hzero
  refine ⟨v, hvU, hvpos, ?_⟩
  obtain ⟨hfinite, hbudget⟩ :=
    positive_equilibria_finite_and_ncard_le_two_n
      (ratesAdd k (selectedRates v)) hn hvpos ET FT ST hET hFT
  dsimp at hfinite hbudget ⊢
  exact ⟨hfinite, hbudget,
    fun x hx => hvregular x hx.1 hx.2.2 hx.2.1⟩

end
end PhosphorylationStableCapacity
