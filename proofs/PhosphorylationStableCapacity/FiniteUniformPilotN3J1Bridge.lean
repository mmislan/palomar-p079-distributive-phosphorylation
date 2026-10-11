module
public import proofs.PhosphorylationStableCapacity.FiniteUniformPilotN3J1Data
public import proofs.PhosphorylationStableCapacity.FiniteFixedRationalInputBridgeM2

@[expose] public section

namespace PhosphorylationStableCapacity
noncomputable section
open PhosphorylationSharpness
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

/-- Every rational matrix entry is checked against the grouped manuscript
rates and the same printed state. -/
theorem uniformPilotN3J1RationalMatrix_eq :
    rationalJacobianMatrix 8 2 10 finiteFixedRatesQM2
      (finiteFixedCoordinatesQM2 1) = uniformPilotN3J1A.ratMatrix := by
  decide +kernel

/-- The certificate matrix is the actual class-chart Jacobian, in the
canonical finite coordinate order. -/
theorem uniformPilotN3J1ActualMatrix_eq :
    allSiteExplicitFinMatrix 8 2 10 (finiteFixedPrintedRates 2)
      (toCoordinateSpace (chart (finiteFixedPrintedState 2 1))) =
        uniformPilotN3J1A.realMatrix := by
  have h := rationalJacobianMatrix_cast (8 : ℚ) (2 : ℚ) (10 : ℚ)
    finiteFixedRatesQM2 (finiteFixedCoordinatesQM2 1)
  rw [uniformPilotN3J1RationalMatrix_eq, ScaledIntegerMatrix.ratMatrix_cast,
    finiteFixedRatesQM2_toReal, finiteFixedCoordinatesQM2_toReal] at h
  norm_num at h
  exact h.symm

end
end PhosphorylationStableCapacity
