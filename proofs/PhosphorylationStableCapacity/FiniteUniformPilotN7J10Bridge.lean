module
public import proofs.PhosphorylationStableCapacity.FiniteUniformPilotN7J10Data
public import proofs.PhosphorylationStableCapacity.FiniteFixedRationalInputBridgeM6

@[expose] public section

namespace PhosphorylationStableCapacity
noncomputable section
open PhosphorylationSharpness
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

/-- Every rational matrix entry is checked against the grouped manuscript
rates and the same printed state. -/
theorem uniformPilotN7J10RationalMatrix_eq :
    rationalJacobianMatrix 16 2 18 finiteFixedRatesQM6
      (finiteFixedCoordinatesQM6 10) = uniformPilotN7J10A.ratMatrix := by
  decide +kernel

/-- The certificate matrix is the actual class-chart Jacobian, in the
canonical finite coordinate order. -/
theorem uniformPilotN7J10ActualMatrix_eq :
    allSiteExplicitFinMatrix 16 2 18 (finiteFixedPrintedRates 6)
      (toCoordinateSpace (chart (finiteFixedPrintedState 6 10))) =
        uniformPilotN7J10A.realMatrix := by
  have h := rationalJacobianMatrix_cast (16 : ℚ) (2 : ℚ) (18 : ℚ)
    finiteFixedRatesQM6 (finiteFixedCoordinatesQM6 10)
  rw [uniformPilotN7J10RationalMatrix_eq, ScaledIntegerMatrix.ratMatrix_cast,
    finiteFixedRatesQM6_toReal, finiteFixedCoordinatesQM6_toReal] at h
  norm_num at h
  exact h.symm

end
end PhosphorylationStableCapacity
