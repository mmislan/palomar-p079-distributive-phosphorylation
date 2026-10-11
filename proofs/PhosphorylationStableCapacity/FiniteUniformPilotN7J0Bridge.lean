module
public import proofs.PhosphorylationStableCapacity.FiniteUniformPilotN7J0Data
public import proofs.PhosphorylationStableCapacity.FiniteFixedRationalInputBridgeM6

@[expose] public section

namespace PhosphorylationStableCapacity
noncomputable section
open PhosphorylationSharpness
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

/-- Every rational matrix entry is checked against the grouped manuscript
rates and the same printed state. -/
theorem uniformPilotN7J0RationalMatrix_eq :
    rationalJacobianMatrix 16 2 18 finiteFixedRatesQM6
      (finiteFixedCoordinatesQM6 0) = uniformPilotN7J0A.ratMatrix := by
  decide +kernel

/-- The certificate matrix is the actual class-chart Jacobian, in the
canonical finite coordinate order. -/
theorem uniformPilotN7J0ActualMatrix_eq :
    allSiteExplicitFinMatrix 16 2 18 (finiteFixedPrintedRates 6)
      (toCoordinateSpace (chart (finiteFixedPrintedState 6 0))) =
        uniformPilotN7J0A.realMatrix := by
  have h := rationalJacobianMatrix_cast (16 : ℚ) (2 : ℚ) (18 : ℚ)
    finiteFixedRatesQM6 (finiteFixedCoordinatesQM6 0)
  rw [uniformPilotN7J0RationalMatrix_eq, ScaledIntegerMatrix.ratMatrix_cast,
    finiteFixedRatesQM6_toReal, finiteFixedCoordinatesQM6_toReal] at h
  norm_num at h
  exact h.symm

end
end PhosphorylationStableCapacity
