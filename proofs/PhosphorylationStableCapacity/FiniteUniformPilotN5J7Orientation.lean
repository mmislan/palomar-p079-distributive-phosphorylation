module
public import proofs.PhosphorylationStableCapacity.FiniteUniformPilotN5J7Bridge
public import proofs.PhosphorylationStableCapacity.FiniteRationalMomentOrientation
public import proofs.PhosphorylationStableCapacity.FiniteFixedPrintedFullSource

@[expose] public section

namespace PhosphorylationStableCapacity
noncomputable section
open PhosphorylationSharpness
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

theorem uniformPilotN5J7A_charpoly_eq_actual :
    uniformPilotN5J7A.realMatrix.charpoly = (restrictedJacobianMatrix 16 2 18 (finiteFixedPrintedRates 4) (toCoordinateSpace (chart (finiteFixedPrintedState 4 7)))).charpoly := by
  have h := congrArg Matrix.charpoly uniformPilotN5J7ActualMatrix_eq.symm
  rw [allSiteExplicitFinMatrix_charpoly_eq_restricted] at h
  exact h

theorem uniformPilotN5J7actualSource :
    (finiteFixedPrintedRates 4).Positive ∧
    (finiteFixedPrintedState 4 7).Positive ∧
    Equilibrium (finiteFixedPrintedRates 4) (finiteFixedPrintedState 4 7) ∧
    InClass 16 2 18 (finiteFixedPrintedState 4 7) := by
  have h := finiteFixedPrinted_complete_source 4 (by decide) (by decide)
  have hs := h.2.2.1 (7 : Fin 9)
  have hr : finiteFixedRadius 4 = (8 : ℝ) := by norm_num [finiteFixedRadius]
  have hc := hs.2.2.2
  rw [hr] at hc
  norm_num at hc
  exact ⟨h.2.1, hs.2.1, hs.2.2.1, hc⟩

/-- Closed rational arithmetic checks the tiny orientation sign exactly. -/
theorem uniformPilotN5J7rationalMomentSign : rationalPhysicalMomentBracket 16 2 18 (finiteFixedCoordinatesQM4 7) < 0 := by
  decide +kernel

theorem uniformPilotN5J7A_constantSign : uniformPilotN5J7A.realMatrix.charpoly.coeff 0 < 0 := by
  have hs := uniformPilotN5J7actualSource
  have h := rational_moment_negative_charpoly_constant
    (16 : ℚ) (2 : ℚ) (18 : ℚ) (finiteFixedCoordinatesQM4 7)
    (finiteFixedPrintedRates 4) (finiteFixedPrintedState 4 7)
    hs.1 hs.2.1 hs.2.2.1 hs.2.2.2
    (finiteFixedCoordinatesQM4_toReal 7) uniformPilotN5J7rationalMomentSign
  rw [uniformPilotN5J7A_charpoly_eq_actual]
  exact h

end
end PhosphorylationStableCapacity
