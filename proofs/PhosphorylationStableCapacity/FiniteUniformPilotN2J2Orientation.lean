module
public import proofs.PhosphorylationStableCapacity.FiniteUniformPilotN2J2Bridge
public import proofs.PhosphorylationStableCapacity.FiniteRationalMomentOrientation
public import proofs.PhosphorylationStableCapacity.FiniteFixedPrintedFullSource

@[expose] public section

namespace PhosphorylationStableCapacity
noncomputable section
open PhosphorylationSharpness
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

theorem uniformPilotN2J2A_charpoly_eq_actual :
    uniformPilotN2J2A.realMatrix.charpoly = (restrictedJacobianMatrix 4 2 6 (finiteFixedPrintedRates 1) (toCoordinateSpace (chart (finiteFixedPrintedState 1 2)))).charpoly := by
  have h := congrArg Matrix.charpoly uniformPilotN2J2ActualMatrix_eq.symm
  rw [allSiteExplicitFinMatrix_charpoly_eq_restricted] at h
  exact h

theorem uniformPilotN2J2actualSource :
    (finiteFixedPrintedRates 1).Positive ∧
    (finiteFixedPrintedState 1 2).Positive ∧
    Equilibrium (finiteFixedPrintedRates 1) (finiteFixedPrintedState 1 2) ∧
    InClass 4 2 6 (finiteFixedPrintedState 1 2) := by
  have h := finiteFixedPrinted_complete_source 1 (by decide) (by decide)
  have hs := h.2.2.1 (2 : Fin 3)
  have hr : finiteFixedRadius 1 = (2 : ℝ) := by norm_num [finiteFixedRadius]
  have hc := hs.2.2.2
  rw [hr] at hc
  norm_num at hc
  exact ⟨h.2.1, hs.2.1, hs.2.2.1, hc⟩

/-- Closed rational arithmetic checks the tiny orientation sign exactly. -/
theorem uniformPilotN2J2rationalMomentSign : 0 < rationalPhysicalMomentBracket 4 2 6 (finiteFixedCoordinatesQM1 2) := by
  decide +kernel

theorem uniformPilotN2J2A_constantSign : 0 < uniformPilotN2J2A.realMatrix.charpoly.coeff 0 := by
  have hs := uniformPilotN2J2actualSource
  have h := rational_moment_positive_charpoly_constant
    (4 : ℚ) (2 : ℚ) (6 : ℚ) (finiteFixedCoordinatesQM1 2)
    (finiteFixedPrintedRates 1) (finiteFixedPrintedState 1 2)
    hs.1 hs.2.1 hs.2.2.1 hs.2.2.2
    (finiteFixedCoordinatesQM1_toReal 2) uniformPilotN2J2rationalMomentSign
  rw [uniformPilotN2J2A_charpoly_eq_actual]
  exact h

end
end PhosphorylationStableCapacity
