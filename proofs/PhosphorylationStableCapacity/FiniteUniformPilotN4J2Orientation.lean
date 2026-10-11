module
public import proofs.PhosphorylationStableCapacity.FiniteUniformPilotN4J2Bridge
public import proofs.PhosphorylationStableCapacity.FiniteRationalMomentOrientation
public import proofs.PhosphorylationStableCapacity.FiniteFixedPrintedFullSource

@[expose] public section

namespace PhosphorylationStableCapacity
noncomputable section
open PhosphorylationSharpness
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

theorem uniformPilotN4J2A_charpoly_eq_actual :
    uniformPilotN4J2A.realMatrix.charpoly = (restrictedJacobianMatrix 8 2 10 (finiteFixedPrintedRates 3) (toCoordinateSpace (chart (finiteFixedPrintedState 3 2)))).charpoly := by
  have h := congrArg Matrix.charpoly uniformPilotN4J2ActualMatrix_eq.symm
  rw [allSiteExplicitFinMatrix_charpoly_eq_restricted] at h
  exact h

theorem uniformPilotN4J2actualSource :
    (finiteFixedPrintedRates 3).Positive ∧
    (finiteFixedPrintedState 3 2).Positive ∧
    Equilibrium (finiteFixedPrintedRates 3) (finiteFixedPrintedState 3 2) ∧
    InClass 8 2 10 (finiteFixedPrintedState 3 2) := by
  have h := finiteFixedPrinted_complete_source 3 (by decide) (by decide)
  have hs := h.2.2.1 (2 : Fin 7)
  have hr : finiteFixedRadius 3 = (4 : ℝ) := by norm_num [finiteFixedRadius]
  have hc := hs.2.2.2
  rw [hr] at hc
  norm_num at hc
  exact ⟨h.2.1, hs.2.1, hs.2.2.1, hc⟩

/-- Closed rational arithmetic checks the tiny orientation sign exactly. -/
theorem uniformPilotN4J2rationalMomentSign : 0 < rationalPhysicalMomentBracket 8 2 10 (finiteFixedCoordinatesQM3 2) := by
  decide +kernel

theorem uniformPilotN4J2A_constantSign : 0 < uniformPilotN4J2A.realMatrix.charpoly.coeff 0 := by
  have hs := uniformPilotN4J2actualSource
  have h := rational_moment_positive_charpoly_constant
    (8 : ℚ) (2 : ℚ) (10 : ℚ) (finiteFixedCoordinatesQM3 2)
    (finiteFixedPrintedRates 3) (finiteFixedPrintedState 3 2)
    hs.1 hs.2.1 hs.2.2.1 hs.2.2.2
    (finiteFixedCoordinatesQM3_toReal 2) uniformPilotN4J2rationalMomentSign
  rw [uniformPilotN4J2A_charpoly_eq_actual]
  exact h

end
end PhosphorylationStableCapacity
