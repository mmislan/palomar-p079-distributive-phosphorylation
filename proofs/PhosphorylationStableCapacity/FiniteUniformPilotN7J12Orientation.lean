module
public import proofs.PhosphorylationStableCapacity.FiniteUniformPilotN7J12Bridge
public import proofs.PhosphorylationStableCapacity.FiniteRationalMomentOrientation
public import proofs.PhosphorylationStableCapacity.FiniteFixedPrintedFullSource

@[expose] public section

namespace PhosphorylationStableCapacity
noncomputable section
open PhosphorylationSharpness
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

theorem uniformPilotN7J12A_charpoly_eq_actual :
    uniformPilotN7J12A.realMatrix.charpoly = (restrictedJacobianMatrix 16 2 18 (finiteFixedPrintedRates 6) (toCoordinateSpace (chart (finiteFixedPrintedState 6 12)))).charpoly := by
  have h := congrArg Matrix.charpoly uniformPilotN7J12ActualMatrix_eq.symm
  rw [allSiteExplicitFinMatrix_charpoly_eq_restricted] at h
  exact h

theorem uniformPilotN7J12actualSource :
    (finiteFixedPrintedRates 6).Positive ∧
    (finiteFixedPrintedState 6 12).Positive ∧
    Equilibrium (finiteFixedPrintedRates 6) (finiteFixedPrintedState 6 12) ∧
    InClass 16 2 18 (finiteFixedPrintedState 6 12) := by
  have h := finiteFixedPrinted_complete_source 6 (by decide) (by decide)
  have hs := h.2.2.1 (12 : Fin 13)
  have hr : finiteFixedRadius 6 = (8 : ℝ) := by norm_num [finiteFixedRadius]
  have hc := hs.2.2.2
  rw [hr] at hc
  norm_num at hc
  exact ⟨h.2.1, hs.2.1, hs.2.2.1, hc⟩

/-- Closed rational arithmetic checks the tiny orientation sign exactly. -/
theorem uniformPilotN7J12rationalMomentSign : 0 < rationalPhysicalMomentBracket 16 2 18 (finiteFixedCoordinatesQM6 12) := by
  decide +kernel

theorem uniformPilotN7J12A_constantSign : 0 < uniformPilotN7J12A.realMatrix.charpoly.coeff 0 := by
  have hs := uniformPilotN7J12actualSource
  have h := rational_moment_positive_charpoly_constant
    (16 : ℚ) (2 : ℚ) (18 : ℚ) (finiteFixedCoordinatesQM6 12)
    (finiteFixedPrintedRates 6) (finiteFixedPrintedState 6 12)
    hs.1 hs.2.1 hs.2.2.1 hs.2.2.2
    (finiteFixedCoordinatesQM6_toReal 12) uniformPilotN7J12rationalMomentSign
  rw [uniformPilotN7J12A_charpoly_eq_actual]
  exact h

end
end PhosphorylationStableCapacity
