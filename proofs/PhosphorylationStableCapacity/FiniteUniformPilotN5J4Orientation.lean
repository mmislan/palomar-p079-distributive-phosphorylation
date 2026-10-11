module
public import proofs.PhosphorylationStableCapacity.FiniteUniformPilotN5J4Bridge
public import proofs.PhosphorylationStableCapacity.FiniteRationalMomentOrientation
public import proofs.PhosphorylationStableCapacity.FiniteFixedPrintedFullSource

@[expose] public section

namespace PhosphorylationStableCapacity
noncomputable section
open PhosphorylationSharpness
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

theorem uniformPilotN5J4A_charpoly_eq_actual :
    uniformPilotN5J4A.realMatrix.charpoly = (restrictedJacobianMatrix 16 2 18 (finiteFixedPrintedRates 4) (toCoordinateSpace (chart (finiteFixedPrintedState 4 4)))).charpoly := by
  have h := congrArg Matrix.charpoly uniformPilotN5J4ActualMatrix_eq.symm
  rw [allSiteExplicitFinMatrix_charpoly_eq_restricted] at h
  exact h

theorem uniformPilotN5J4actualSource :
    (finiteFixedPrintedRates 4).Positive ∧
    (finiteFixedPrintedState 4 4).Positive ∧
    Equilibrium (finiteFixedPrintedRates 4) (finiteFixedPrintedState 4 4) ∧
    InClass 16 2 18 (finiteFixedPrintedState 4 4) := by
  have h := finiteFixedPrinted_complete_source 4 (by decide) (by decide)
  have hs := h.2.2.1 (4 : Fin 9)
  have hr : finiteFixedRadius 4 = (8 : ℝ) := by norm_num [finiteFixedRadius]
  have hc := hs.2.2.2
  rw [hr] at hc
  norm_num at hc
  exact ⟨h.2.1, hs.2.1, hs.2.2.1, hc⟩

/-- Closed rational arithmetic checks the tiny orientation sign exactly. -/
theorem uniformPilotN5J4rationalMomentSign : 0 < rationalPhysicalMomentBracket 16 2 18 (finiteFixedCoordinatesQM4 4) := by
  decide +kernel

theorem uniformPilotN5J4A_constantSign : 0 < uniformPilotN5J4A.realMatrix.charpoly.coeff 0 := by
  have hs := uniformPilotN5J4actualSource
  have h := rational_moment_positive_charpoly_constant
    (16 : ℚ) (2 : ℚ) (18 : ℚ) (finiteFixedCoordinatesQM4 4)
    (finiteFixedPrintedRates 4) (finiteFixedPrintedState 4 4)
    hs.1 hs.2.1 hs.2.2.1 hs.2.2.2
    (finiteFixedCoordinatesQM4_toReal 4) uniformPilotN5J4rationalMomentSign
  rw [uniformPilotN5J4A_charpoly_eq_actual]
  exact h

end
end PhosphorylationStableCapacity
