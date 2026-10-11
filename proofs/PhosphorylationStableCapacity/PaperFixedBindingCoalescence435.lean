module
public import proofs.PhosphorylationStableCapacity.PaperFixedBindingSplitCount435
public import proofs.PhosphorylationStableCapacity.ArbitrarySplitStateContinuity

@[expose] public section

namespace PhosphorylationStableCapacity
noncomputable section
open PhosphorylationSharpness

/-- The literal fixed-binding split Jacobian coalesces to the selected
neutral matrix on the same state, rates, and compatibility class. -/
theorem paperFixedBindingSplit_restrictedJacobianMatrix_zero_eq_coalesced
    (m : ℕ) (ξ : ℕ → ℝ) (r ε : ℝ)
    (w : Fin (m+2) → ℝ) (j : Fin (2*(m+1)+1)) :
    restrictedJacobianMatrix (2*r) 2 (2*(r+1))
      (paperFixedBindingSplitRates m ξ r 0 ε w)
      (toCoordinateSpace (chart
        (arbitrarySplitFiniteState (m+1) ξ r 0 j))) =
    restrictedJacobianMatrix (2*r) 2 (2*(r+1))
      (relaxRates (paperFixedBindingRates
        (coalescedAllScaledRates m r w)) ε)
      (fromLoadedCoord (loadedCoordOfState
        (coalescedFiniteState (m+1) r))) := by
  simp [paperFixedBindingSplitRates, coalescedAllScaledRates,
    arbitrarySplitFiniteRates_zero_eq_coalesced,
    arbitrarySplitFiniteState_zero_eq_coalesced,
    loadedCoordOfState, from_toLoadedCoord]

end
end PhosphorylationStableCapacity
