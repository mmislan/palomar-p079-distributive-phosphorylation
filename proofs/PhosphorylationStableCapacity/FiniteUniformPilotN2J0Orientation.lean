module
public import proofs.PhosphorylationStableCapacity.FiniteUniformPilotN2J0Bridge
public import proofs.PhosphorylationStableCapacity.FiniteRationalMomentOrientation
public import proofs.PhosphorylationStableCapacity.FiniteFixedPrintedFullSource

@[expose] public section

namespace PhosphorylationStableCapacity
noncomputable section
open PhosphorylationSharpness
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

theorem uniformPilotN2J0A_charpoly_eq_actual :
    uniformPilotN2J0A.realMatrix.charpoly = (restrictedJacobianMatrix 4 2 6 (finiteFixedPrintedRates 1) (toCoordinateSpace (chart (finiteFixedPrintedState 1 0)))).charpoly := by
  have h := congrArg Matrix.charpoly uniformPilotN2J0ActualMatrix_eq.symm
  rw [allSiteExplicitFinMatrix_charpoly_eq_restricted] at h
  exact h

theorem uniformPilotN2J0actualSource :
    (finiteFixedPrintedRates 1).Positive ∧
    (finiteFixedPrintedState 1 0).Positive ∧
    Equilibrium (finiteFixedPrintedRates 1) (finiteFixedPrintedState 1 0) ∧
    InClass 4 2 6 (finiteFixedPrintedState 1 0) := by
  have h := finiteFixedPrinted_complete_source 1 (by decide) (by decide)
  have hs := h.2.2.1 (0 : Fin 3)
  have hr : finiteFixedRadius 1 = (2 : ℝ) := by norm_num [finiteFixedRadius]
  have hc := hs.2.2.2
  rw [hr] at hc
  norm_num at hc
  exact ⟨h.2.1, hs.2.1, hs.2.2.1, hc⟩

/-- Closed rational arithmetic checks the tiny orientation sign exactly. -/
theorem uniformPilotN2J0rationalMomentSign : 0 < rationalPhysicalMomentBracket 4 2 6 (finiteFixedCoordinatesQM1 0) := by
  decide +kernel

theorem uniformPilotN2J0A_constantSign : 0 < uniformPilotN2J0A.realMatrix.charpoly.coeff 0 := by
  have hs := uniformPilotN2J0actualSource
  have h := rational_moment_positive_charpoly_constant
    (4 : ℚ) (2 : ℚ) (6 : ℚ) (finiteFixedCoordinatesQM1 0)
    (finiteFixedPrintedRates 1) (finiteFixedPrintedState 1 0)
    hs.1 hs.2.1 hs.2.2.1 hs.2.2.2
    (finiteFixedCoordinatesQM1_toReal 0) uniformPilotN2J0rationalMomentSign
  rw [uniformPilotN2J0A_charpoly_eq_actual]
  exact h

end
end PhosphorylationStableCapacity
