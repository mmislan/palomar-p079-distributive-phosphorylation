module
public import proofs.PhosphorylationStableCapacity.FiniteUniformPilotN4J1Data
public import proofs.PhosphorylationStableCapacity.FiniteFixedRationalInputBridgeM3

@[expose] public section

namespace PhosphorylationStableCapacity
noncomputable section
open PhosphorylationSharpness
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

/-- Every rational matrix entry is checked against the grouped manuscript
rates and the same printed state. -/
theorem uniformPilotN4J1RationalMatrix_eq :
    rationalJacobianMatrix 8 2 10 finiteFixedRatesQM3
      (finiteFixedCoordinatesQM3 1) = uniformPilotN4J1A.ratMatrix := by
  decide +kernel

/-- The certificate matrix is the actual class-chart Jacobian, in the
canonical finite coordinate order. -/
theorem uniformPilotN4J1ActualMatrix_eq :
    allSiteExplicitFinMatrix 8 2 10 (finiteFixedPrintedRates 3)
      (toCoordinateSpace (chart (finiteFixedPrintedState 3 1))) =
        uniformPilotN4J1A.realMatrix := by
  have h := rationalJacobianMatrix_cast (8 : ℚ) (2 : ℚ) (10 : ℚ)
    finiteFixedRatesQM3 (finiteFixedCoordinatesQM3 1)
  rw [uniformPilotN4J1RationalMatrix_eq, ScaledIntegerMatrix.ratMatrix_cast,
    finiteFixedRatesQM3_toReal, finiteFixedCoordinatesQM3_toReal] at h
  norm_num at h
  exact h.symm

end
end PhosphorylationStableCapacity
