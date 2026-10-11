module
public import proofs.PhosphorylationStableCapacity.FiniteUniformPilotN4J6Bridge
public import proofs.PhosphorylationStableCapacity.FiniteRationalMomentOrientation
public import proofs.PhosphorylationStableCapacity.FiniteFixedPrintedFullSource

@[expose] public section

namespace PhosphorylationStableCapacity
noncomputable section
open PhosphorylationSharpness
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

theorem uniformPilotN4J6A_charpoly_eq_actual :
    uniformPilotN4J6A.realMatrix.charpoly = (restrictedJacobianMatrix 8 2 10 (finiteFixedPrintedRates 3) (toCoordinateSpace (chart (finiteFixedPrintedState 3 6)))).charpoly := by
  have h := congrArg Matrix.charpoly uniformPilotN4J6ActualMatrix_eq.symm
  rw [allSiteExplicitFinMatrix_charpoly_eq_restricted] at h
  exact h

theorem uniformPilotN4J6actualSource :
    (finiteFixedPrintedRates 3).Positive ∧
    (finiteFixedPrintedState 3 6).Positive ∧
    Equilibrium (finiteFixedPrintedRates 3) (finiteFixedPrintedState 3 6) ∧
    InClass 8 2 10 (finiteFixedPrintedState 3 6) := by
  have h := finiteFixedPrinted_complete_source 3 (by decide) (by decide)
  have hs := h.2.2.1 (6 : Fin 7)
  have hr : finiteFixedRadius 3 = (4 : ℝ) := by norm_num [finiteFixedRadius]
  have hc := hs.2.2.2
  rw [hr] at hc
  norm_num at hc
  exact ⟨h.2.1, hs.2.1, hs.2.2.1, hc⟩

/-- Closed rational arithmetic checks the tiny orientation sign exactly. -/
theorem uniformPilotN4J6rationalMomentSign : 0 < rationalPhysicalMomentBracket 8 2 10 (finiteFixedCoordinatesQM3 6) := by
  decide +kernel

theorem uniformPilotN4J6A_constantSign : 0 < uniformPilotN4J6A.realMatrix.charpoly.coeff 0 := by
  have hs := uniformPilotN4J6actualSource
  have h := rational_moment_positive_charpoly_constant
    (8 : ℚ) (2 : ℚ) (10 : ℚ) (finiteFixedCoordinatesQM3 6)
    (finiteFixedPrintedRates 3) (finiteFixedPrintedState 3 6)
    hs.1 hs.2.1 hs.2.2.1 hs.2.2.2
    (finiteFixedCoordinatesQM3_toReal 6) uniformPilotN4J6rationalMomentSign
  rw [uniformPilotN4J6A_charpoly_eq_actual]
  exact h

end
end PhosphorylationStableCapacity
