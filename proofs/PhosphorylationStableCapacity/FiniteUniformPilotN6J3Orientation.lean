module
public import proofs.PhosphorylationStableCapacity.FiniteUniformPilotN6J3Bridge
public import proofs.PhosphorylationStableCapacity.FiniteRationalMomentOrientation
public import proofs.PhosphorylationStableCapacity.FiniteFixedPrintedFullSource

@[expose] public section

namespace PhosphorylationStableCapacity
noncomputable section
open PhosphorylationSharpness
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

theorem uniformPilotN6J3A_charpoly_eq_actual :
    uniformPilotN6J3A.realMatrix.charpoly = (restrictedJacobianMatrix 16 2 18 (finiteFixedPrintedRates 5) (toCoordinateSpace (chart (finiteFixedPrintedState 5 3)))).charpoly := by
  have h := congrArg Matrix.charpoly uniformPilotN6J3ActualMatrix_eq.symm
  rw [allSiteExplicitFinMatrix_charpoly_eq_restricted] at h
  exact h

theorem uniformPilotN6J3actualSource :
    (finiteFixedPrintedRates 5).Positive ∧
    (finiteFixedPrintedState 5 3).Positive ∧
    Equilibrium (finiteFixedPrintedRates 5) (finiteFixedPrintedState 5 3) ∧
    InClass 16 2 18 (finiteFixedPrintedState 5 3) := by
  have h := finiteFixedPrinted_complete_source 5 (by decide) (by decide)
  have hs := h.2.2.1 (3 : Fin 11)
  have hr : finiteFixedRadius 5 = (8 : ℝ) := by norm_num [finiteFixedRadius]
  have hc := hs.2.2.2
  rw [hr] at hc
  norm_num at hc
  exact ⟨h.2.1, hs.2.1, hs.2.2.1, hc⟩

/-- Closed rational arithmetic checks the tiny orientation sign exactly. -/
theorem uniformPilotN6J3rationalMomentSign : rationalPhysicalMomentBracket 16 2 18 (finiteFixedCoordinatesQM5 3) < 0 := by
  decide +kernel

theorem uniformPilotN6J3A_constantSign : uniformPilotN6J3A.realMatrix.charpoly.coeff 0 < 0 := by
  have hs := uniformPilotN6J3actualSource
  have h := rational_moment_negative_charpoly_constant
    (16 : ℚ) (2 : ℚ) (18 : ℚ) (finiteFixedCoordinatesQM5 3)
    (finiteFixedPrintedRates 5) (finiteFixedPrintedState 5 3)
    hs.1 hs.2.1 hs.2.2.1 hs.2.2.2
    (finiteFixedCoordinatesQM5_toReal 3) uniformPilotN6J3rationalMomentSign
  rw [uniformPilotN6J3A_charpoly_eq_actual]
  exact h

end
end PhosphorylationStableCapacity
