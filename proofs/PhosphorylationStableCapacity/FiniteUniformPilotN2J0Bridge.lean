module
public import proofs.PhosphorylationStableCapacity.FiniteUniformPilotN2J0Data
public import proofs.PhosphorylationStableCapacity.FiniteFixedRationalInputBridgeM1

@[expose] public section

namespace PhosphorylationStableCapacity
noncomputable section
open PhosphorylationSharpness
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

/-- Every rational matrix entry is checked against the grouped manuscript
rates and the same printed state. -/
theorem uniformPilotN2J0RationalMatrix_eq :
    rationalJacobianMatrix 4 2 6 finiteFixedRatesQM1
      (finiteFixedCoordinatesQM1 0) = uniformPilotN2J0A.ratMatrix := by
  decide +kernel

/-- The certificate matrix is the actual class-chart Jacobian, in the
canonical finite coordinate order. -/
theorem uniformPilotN2J0ActualMatrix_eq :
    allSiteExplicitFinMatrix 4 2 6 (finiteFixedPrintedRates 1)
      (toCoordinateSpace (chart (finiteFixedPrintedState 1 0))) =
        uniformPilotN2J0A.realMatrix := by
  have h := rationalJacobianMatrix_cast (4 : ℚ) (2 : ℚ) (6 : ℚ)
    finiteFixedRatesQM1 (finiteFixedCoordinatesQM1 0)
  rw [uniformPilotN2J0RationalMatrix_eq, ScaledIntegerMatrix.ratMatrix_cast,
    finiteFixedRatesQM1_toReal, finiteFixedCoordinatesQM1_toReal] at h
  norm_num at h
  exact h.symm

end
end PhosphorylationStableCapacity
