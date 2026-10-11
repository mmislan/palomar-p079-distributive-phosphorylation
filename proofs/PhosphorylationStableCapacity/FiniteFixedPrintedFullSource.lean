module
public import proofs.PhosphorylationStableCapacity.FiniteFixedPrintedCoefficients
public import proofs.PhosphorylationStableCapacity.FiniteFixedPrintedEndpoint

@[expose] public section

namespace PhosphorylationStableCapacity
noncomputable section
open PhosphorylationSharpness

/-- Every printed size has one common rational positive rate vector, the
full rational positive equilibrium list, and exact exhaustion. All finite
coefficient inputs are discharged by the explicit six-size certificates. -/
theorem finiteFixedPrinted_complete_source
    (m : ℕ) (hm : 1 ≤ m) (hm6 : m ≤ 6) :
    RationalRates (finiteFixedPrintedRates m) ∧
      (finiteFixedPrintedRates m).Positive ∧
      (∀ j : Fin (2*m+1), RationalState (finiteFixedPrintedState m j) ∧
        (finiteFixedPrintedState m j).Positive ∧
        Equilibrium (finiteFixedPrintedRates m) (finiteFixedPrintedState m j) ∧
        InClass (2*finiteFixedRadius m) 2 (2*(finiteFixedRadius m+1))
          (finiteFixedPrintedState m j)) ∧
      Function.Injective (finiteFixedPrintedState m) ∧
      {s : State (m+1) | s.Positive ∧ Equilibrium (finiteFixedPrintedRates m) s ∧
        InClass (2*finiteFixedRadius m) 2 (2*(finiteFixedRadius m+1)) s} =
          Set.range (finiteFixedPrintedState m) ∧
      {s : State (m+1) | s.Positive ∧ Equilibrium (finiteFixedPrintedRates m) s ∧
        InClass (2*finiteFixedRadius m) 2 (2*(finiteFixedRadius m+1)) s}.ncard =
          2*m+1 := by
  obtain ⟨hD, hB, hcoalD⟩ := finiteFixedPrinted_coefficients_positive m hm hm6
  exact finiteFixedPrinted_complete_source_of_coeff_positive m hm hm6 hD hB hcoalD

end
end PhosphorylationStableCapacity
