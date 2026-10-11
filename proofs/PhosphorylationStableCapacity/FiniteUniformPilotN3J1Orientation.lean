module
public import proofs.PhosphorylationStableCapacity.FiniteUniformPilotN3J1Bridge
public import proofs.PhosphorylationStableCapacity.FiniteRationalMomentOrientation
public import proofs.PhosphorylationStableCapacity.FiniteFixedPrintedFullSource

@[expose] public section

namespace PhosphorylationStableCapacity
noncomputable section
open PhosphorylationSharpness
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

theorem uniformPilotN3J1A_charpoly_eq_actual :
    uniformPilotN3J1A.realMatrix.charpoly = (restrictedJacobianMatrix 8 2 10 (finiteFixedPrintedRates 2) (toCoordinateSpace (chart (finiteFixedPrintedState 2 1)))).charpoly := by
  have h := congrArg Matrix.charpoly uniformPilotN3J1ActualMatrix_eq.symm
  rw [allSiteExplicitFinMatrix_charpoly_eq_restricted] at h
  exact h

theorem uniformPilotN3J1actualSource :
    (finiteFixedPrintedRates 2).Positive ∧
    (finiteFixedPrintedState 2 1).Positive ∧
    Equilibrium (finiteFixedPrintedRates 2) (finiteFixedPrintedState 2 1) ∧
    InClass 8 2 10 (finiteFixedPrintedState 2 1) := by
  have h := finiteFixedPrinted_complete_source 2 (by decide) (by decide)
  have hs := h.2.2.1 (1 : Fin 5)
  have hr : finiteFixedRadius 2 = (4 : ℝ) := by norm_num [finiteFixedRadius]
  have hc := hs.2.2.2
  rw [hr] at hc
  norm_num at hc
  exact ⟨h.2.1, hs.2.1, hs.2.2.1, hc⟩

/-- Closed rational arithmetic checks the tiny orientation sign exactly. -/
theorem uniformPilotN3J1rationalMomentSign : rationalPhysicalMomentBracket 8 2 10 (finiteFixedCoordinatesQM2 1) < 0 := by
  decide +kernel

theorem uniformPilotN3J1A_constantSign : uniformPilotN3J1A.realMatrix.charpoly.coeff 0 < 0 := by
  have hs := uniformPilotN3J1actualSource
  have h := rational_moment_negative_charpoly_constant
    (8 : ℚ) (2 : ℚ) (10 : ℚ) (finiteFixedCoordinatesQM2 1)
    (finiteFixedPrintedRates 2) (finiteFixedPrintedState 2 1)
    hs.1 hs.2.1 hs.2.2.1 hs.2.2.2
    (finiteFixedCoordinatesQM2_toReal 1) uniformPilotN3J1rationalMomentSign
  rw [uniformPilotN3J1A_charpoly_eq_actual]
  exact h

end
end PhosphorylationStableCapacity
