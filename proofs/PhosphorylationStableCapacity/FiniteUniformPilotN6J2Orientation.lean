module
public import proofs.PhosphorylationStableCapacity.FiniteUniformPilotN6J2Bridge
public import proofs.PhosphorylationStableCapacity.FiniteRationalMomentOrientation
public import proofs.PhosphorylationStableCapacity.FiniteFixedPrintedFullSource

@[expose] public section

namespace PhosphorylationStableCapacity
noncomputable section
open PhosphorylationSharpness
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

theorem uniformPilotN6J2A_charpoly_eq_actual :
    uniformPilotN6J2A.realMatrix.charpoly = (restrictedJacobianMatrix 16 2 18 (finiteFixedPrintedRates 5) (toCoordinateSpace (chart (finiteFixedPrintedState 5 2)))).charpoly := by
  have h := congrArg Matrix.charpoly uniformPilotN6J2ActualMatrix_eq.symm
  rw [allSiteExplicitFinMatrix_charpoly_eq_restricted] at h
  exact h

theorem uniformPilotN6J2actualSource :
    (finiteFixedPrintedRates 5).Positive ∧
    (finiteFixedPrintedState 5 2).Positive ∧
    Equilibrium (finiteFixedPrintedRates 5) (finiteFixedPrintedState 5 2) ∧
    InClass 16 2 18 (finiteFixedPrintedState 5 2) := by
  have h := finiteFixedPrinted_complete_source 5 (by decide) (by decide)
  have hs := h.2.2.1 (2 : Fin 11)
  have hr : finiteFixedRadius 5 = (8 : ℝ) := by norm_num [finiteFixedRadius]
  have hc := hs.2.2.2
  rw [hr] at hc
  norm_num at hc
  exact ⟨h.2.1, hs.2.1, hs.2.2.1, hc⟩

/-- Closed rational arithmetic checks the tiny orientation sign exactly. -/
theorem uniformPilotN6J2rationalMomentSign : 0 < rationalPhysicalMomentBracket 16 2 18 (finiteFixedCoordinatesQM5 2) := by
  decide +kernel

theorem uniformPilotN6J2A_constantSign : 0 < uniformPilotN6J2A.realMatrix.charpoly.coeff 0 := by
  have hs := uniformPilotN6J2actualSource
  have h := rational_moment_positive_charpoly_constant
    (16 : ℚ) (2 : ℚ) (18 : ℚ) (finiteFixedCoordinatesQM5 2)
    (finiteFixedPrintedRates 5) (finiteFixedPrintedState 5 2)
    hs.1 hs.2.1 hs.2.2.1 hs.2.2.2
    (finiteFixedCoordinatesQM5_toReal 2) uniformPilotN6J2rationalMomentSign
  rw [uniformPilotN6J2A_charpoly_eq_actual]
  exact h

end
end PhosphorylationStableCapacity
