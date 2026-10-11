module
public import proofs.PhosphorylationStableCapacity.FiniteUniformPilotN2J2Orientation
public import proofs.PhosphorylationStableCapacity.FiniteUniformPilotN2J2Certificate
public import proofs.PhosphorylationStableCapacity.FiniteSmallGainEvenChecker
public import proofs.PhosphorylationStableCapacity.PositiveRootFromOrientation
public import proofs.PhosphorylationStableCapacity.OddSaddleSpectrum
public import proofs.PhosphorylationStableCapacity.StateHurwitzNonlinearStability

@[expose] public section

namespace PhosphorylationStableCapacity
noncomputable section
open PhosphorylationSharpness

theorem uniformPilotN2J2A_hurwitz : IsHurwitz uniformPilotN2J2A.realMatrix := by
  exact finiteSmallGain_even_hurwitz uniformPilotN2J2A.realMatrix
    uniformPilotN2J2Certificate.complexMatrix (1/8) (1/1000) (1/100) (1/10)
    (by norm_num) uniformPilotN2J2Certificate.complex_charpoly_eq
    uniformPilotN2J2Certificate.row_real uniformPilotN2J2Certificate.column_real
    (by norm_num) (by norm_num) uniformPilotN2J2Certificate.feedback_real (by norm_num)
    uniformPilotN2J2A_constantSign

theorem uniformPilotN2J2actual_linearlyStable :
    IsLinearlyStable 4 2 6 (finiteFixedPrintedRates 1)
      (toCoordinateSpace (chart (finiteFixedPrintedState 1 2))) := by
  intro z hz
  apply uniformPilotN2J2A_hurwitz z
  rw [Matrix.charpoly_map, uniformPilotN2J2A_charpoly_eq_actual, ← Matrix.charpoly_map]
  exact hz

theorem uniformPilotN2J2actual_nonlinearSink :
    IsLocallyAsymptoticallyStableClass 4 2 6 (finiteFixedPrintedRates 1)
      (toCoordinateSpace (chart (finiteFixedPrintedState 1 2))) := by
  have hs := uniformPilotN2J2actualSource
  exact state_linearly_stable_locally_asymptotically_stable
    (by decide) 4 2 6 (by norm_num) (finiteFixedPrintedRates 1)
    hs.1 (finiteFixedPrintedState 1 2) hs.2.1 hs.2.2.1 hs.2.2.2
    uniformPilotN2J2actual_linearlyStable

end
end PhosphorylationStableCapacity
