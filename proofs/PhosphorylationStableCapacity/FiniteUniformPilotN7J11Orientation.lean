module
public import proofs.PhosphorylationStableCapacity.FiniteUniformPilotN7J11Bridge
public import proofs.PhosphorylationStableCapacity.FiniteRationalMomentOrientation
public import proofs.PhosphorylationStableCapacity.FiniteFixedPrintedFullSource

@[expose] public section

namespace PhosphorylationStableCapacity
noncomputable section
open PhosphorylationSharpness
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

theorem uniformPilotN7J11A_charpoly_eq_actual :
    uniformPilotN7J11A.realMatrix.charpoly = (restrictedJacobianMatrix 16 2 18 (finiteFixedPrintedRates 6) (toCoordinateSpace (chart (finiteFixedPrintedState 6 11)))).charpoly := by
  have h := congrArg Matrix.charpoly uniformPilotN7J11ActualMatrix_eq.symm
  rw [allSiteExplicitFinMatrix_charpoly_eq_restricted] at h
  exact h

theorem uniformPilotN7J11actualSource :
    (finiteFixedPrintedRates 6).Positive ∧
    (finiteFixedPrintedState 6 11).Positive ∧
    Equilibrium (finiteFixedPrintedRates 6) (finiteFixedPrintedState 6 11) ∧
    InClass 16 2 18 (finiteFixedPrintedState 6 11) := by
  have h := finiteFixedPrinted_complete_source 6 (by decide) (by decide)
  have hs := h.2.2.1 (11 : Fin 13)
  have hr : finiteFixedRadius 6 = (8 : ℝ) := by norm_num [finiteFixedRadius]
  have hc := hs.2.2.2
  rw [hr] at hc
  norm_num at hc
  exact ⟨h.2.1, hs.2.1, hs.2.2.1, hc⟩

/-- Closed rational arithmetic checks the tiny orientation sign exactly. -/
theorem uniformPilotN7J11rationalMomentSign : rationalPhysicalMomentBracket 16 2 18 (finiteFixedCoordinatesQM6 11) < 0 := by
  decide +kernel

theorem uniformPilotN7J11A_constantSign : uniformPilotN7J11A.realMatrix.charpoly.coeff 0 < 0 := by
  have hs := uniformPilotN7J11actualSource
  have h := rational_moment_negative_charpoly_constant
    (16 : ℚ) (2 : ℚ) (18 : ℚ) (finiteFixedCoordinatesQM6 11)
    (finiteFixedPrintedRates 6) (finiteFixedPrintedState 6 11)
    hs.1 hs.2.1 hs.2.2.1 hs.2.2.2
    (finiteFixedCoordinatesQM6_toReal 11) uniformPilotN7J11rationalMomentSign
  rw [uniformPilotN7J11A_charpoly_eq_actual]
  exact h

end
end PhosphorylationStableCapacity
