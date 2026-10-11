module
public import proofs.PhosphorylationStableCapacity.FiniteUniformPilotN6J0Data
public import proofs.PhosphorylationStableCapacity.FiniteFixedRationalInputBridgeM5

@[expose] public section

namespace PhosphorylationStableCapacity
noncomputable section
open PhosphorylationSharpness
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

/-- Every rational matrix entry is checked against the grouped manuscript
rates and the same printed state. -/
theorem uniformPilotN6J0RationalMatrix_eq :
    rationalJacobianMatrix 16 2 18 finiteFixedRatesQM5
      (finiteFixedCoordinatesQM5 0) = uniformPilotN6J0A.ratMatrix := by
  decide +kernel

/-- The certificate matrix is the actual class-chart Jacobian, in the
canonical finite coordinate order. -/
theorem uniformPilotN6J0ActualMatrix_eq :
    allSiteExplicitFinMatrix 16 2 18 (finiteFixedPrintedRates 5)
      (toCoordinateSpace (chart (finiteFixedPrintedState 5 0))) =
        uniformPilotN6J0A.realMatrix := by
  have h := rationalJacobianMatrix_cast (16 : ℚ) (2 : ℚ) (18 : ℚ)
    finiteFixedRatesQM5 (finiteFixedCoordinatesQM5 0)
  rw [uniformPilotN6J0RationalMatrix_eq, ScaledIntegerMatrix.ratMatrix_cast,
    finiteFixedRatesQM5_toReal, finiteFixedCoordinatesQM5_toReal] at h
  norm_num at h
  exact h.symm

end
end PhosphorylationStableCapacity
