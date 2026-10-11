module
public import proofs.PhosphorylationStableCapacity.FiniteUniformPilotN4J3Bridge
public import proofs.PhosphorylationStableCapacity.FiniteRationalMomentOrientation
public import proofs.PhosphorylationStableCapacity.FiniteFixedPrintedFullSource

@[expose] public section

namespace PhosphorylationStableCapacity
noncomputable section
open PhosphorylationSharpness
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

theorem uniformPilotN4J3A_charpoly_eq_actual :
    uniformPilotN4J3A.realMatrix.charpoly = (restrictedJacobianMatrix 8 2 10 (finiteFixedPrintedRates 3) (toCoordinateSpace (chart (finiteFixedPrintedState 3 3)))).charpoly := by
  have h := congrArg Matrix.charpoly uniformPilotN4J3ActualMatrix_eq.symm
  rw [allSiteExplicitFinMatrix_charpoly_eq_restricted] at h
  exact h

theorem uniformPilotN4J3actualSource :
    (finiteFixedPrintedRates 3).Positive ∧
    (finiteFixedPrintedState 3 3).Positive ∧
    Equilibrium (finiteFixedPrintedRates 3) (finiteFixedPrintedState 3 3) ∧
    InClass 8 2 10 (finiteFixedPrintedState 3 3) := by
  have h := finiteFixedPrinted_complete_source 3 (by decide) (by decide)
  have hs := h.2.2.1 (3 : Fin 7)
  have hr : finiteFixedRadius 3 = (4 : ℝ) := by norm_num [finiteFixedRadius]
  have hc := hs.2.2.2
  rw [hr] at hc
  norm_num at hc
  exact ⟨h.2.1, hs.2.1, hs.2.2.1, hc⟩

/-- Closed rational arithmetic checks the tiny orientation sign exactly. -/
theorem uniformPilotN4J3rationalMomentSign : rationalPhysicalMomentBracket 8 2 10 (finiteFixedCoordinatesQM3 3) < 0 := by
  decide +kernel

theorem uniformPilotN4J3A_constantSign : uniformPilotN4J3A.realMatrix.charpoly.coeff 0 < 0 := by
  have hs := uniformPilotN4J3actualSource
  have h := rational_moment_negative_charpoly_constant
    (8 : ℚ) (2 : ℚ) (10 : ℚ) (finiteFixedCoordinatesQM3 3)
    (finiteFixedPrintedRates 3) (finiteFixedPrintedState 3 3)
    hs.1 hs.2.1 hs.2.2.1 hs.2.2.2
    (finiteFixedCoordinatesQM3_toReal 3) uniformPilotN4J3rationalMomentSign
  rw [uniformPilotN4J3A_charpoly_eq_actual]
  exact h

end
end PhosphorylationStableCapacity
