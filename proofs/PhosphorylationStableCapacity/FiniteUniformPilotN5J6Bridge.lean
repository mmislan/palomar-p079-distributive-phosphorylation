module
public import proofs.PhosphorylationStableCapacity.FiniteUniformPilotN5J6Data
public import proofs.PhosphorylationStableCapacity.FiniteFixedRationalInputBridgeM4

@[expose] public section

namespace PhosphorylationStableCapacity
noncomputable section
open PhosphorylationSharpness
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

/-- Every rational matrix entry is checked against the grouped manuscript
rates and the same printed state. -/
theorem uniformPilotN5J6RationalMatrix_eq :
    rationalJacobianMatrix 16 2 18 finiteFixedRatesQM4
      (finiteFixedCoordinatesQM4 6) = uniformPilotN5J6A.ratMatrix := by
  decide +kernel

/-- The certificate matrix is the actual class-chart Jacobian, in the
canonical finite coordinate order. -/
theorem uniformPilotN5J6ActualMatrix_eq :
    allSiteExplicitFinMatrix 16 2 18 (finiteFixedPrintedRates 4)
      (toCoordinateSpace (chart (finiteFixedPrintedState 4 6))) =
        uniformPilotN5J6A.realMatrix := by
  have h := rationalJacobianMatrix_cast (16 : ℚ) (2 : ℚ) (18 : ℚ)
    finiteFixedRatesQM4 (finiteFixedCoordinatesQM4 6)
  rw [uniformPilotN5J6RationalMatrix_eq, ScaledIntegerMatrix.ratMatrix_cast,
    finiteFixedRatesQM4_toReal, finiteFixedCoordinatesQM4_toReal] at h
  norm_num at h
  exact h.symm

end
end PhosphorylationStableCapacity
