module
public import proofs.PhosphorylationStableCapacity.FiniteFixedTwoSiteCoefficientPilot
public import proofs.PhosphorylationStableCapacity.FiniteFixedThreeSiteCoefficientPilot
public import proofs.PhosphorylationStableCapacity.FiniteFixedFourSiteCoefficientPilot
public import proofs.PhosphorylationStableCapacity.FiniteFixedFiveSiteCoefficientPilot
public import proofs.PhosphorylationStableCapacity.FiniteFixedSixSiteCoefficientPilot
public import proofs.PhosphorylationStableCapacity.FiniteFixedSevenSiteCoefficientPilot

@[expose] public section

namespace PhosphorylationStableCapacity
noncomputable section
open PhosphorylationSharpness

/-- Exhaustive six-size assembly of the actual coefficient certificates. -/
theorem finiteFixedPrinted_coefficients_positive
    (m : ℕ) (hm : 1 ≤ m) (hm6 : m ≤ 6) :
    DensePositive
      (arbitrarySplitRawD m (finiteFixedOffset m)
        (finiteFixedRadius m) (finiteFixedSpacing m)) m ∧
    DensePositive
      (arbitrarySplitRawB m (finiteFixedOffset m)
        (finiteFixedRadius m) (finiteFixedSpacing m)) m ∧
    ∀ i : Fin (m+1),
      0 < (coalescedFiniteState m (finiteFixedRadius m)).D i := by
  interval_cases m
  · exact ⟨finiteFixedTwoSite_coefficients_positive.1,
      finiteFixedTwoSite_coefficients_positive.2,
      finiteFixedTwoSite_coalesced_D_positive⟩
  · exact ⟨finiteFixedThreeSite_coefficients_positive.1,
      finiteFixedThreeSite_coefficients_positive.2,
      finiteFixedThreeSite_coalesced_D_positive⟩
  · exact ⟨finiteFixedFourSite_coefficients_positive.1,
      finiteFixedFourSite_coefficients_positive.2,
      finiteFixedFourSite_coalesced_D_positive⟩
  · exact ⟨finiteFixedFiveSite_coefficients_positive.1,
      finiteFixedFiveSite_coefficients_positive.2,
      finiteFixedFiveSite_coalesced_D_positive⟩
  · exact ⟨finiteFixedSixSite_coefficients_positive.1,
      finiteFixedSixSite_coefficients_positive.2,
      finiteFixedSixSite_coalesced_D_positive⟩
  · exact ⟨finiteFixedSevenSite_coefficients_positive.1,
      finiteFixedSevenSite_coefficients_positive.2,
      finiteFixedSevenSite_coalesced_D_positive⟩

end
end PhosphorylationStableCapacity
