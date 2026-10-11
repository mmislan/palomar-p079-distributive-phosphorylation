module
public import proofs.PhosphorylationStableCapacity.FiniteUniformPilotN2J0Orientation
public import proofs.PhosphorylationStableCapacity.FiniteUniformPilotN2J0Certificate
public import proofs.PhosphorylationStableCapacity.FiniteSmallGainEvenChecker
public import proofs.PhosphorylationStableCapacity.PositiveRootFromOrientation
public import proofs.PhosphorylationStableCapacity.OddSaddleSpectrum
public import proofs.PhosphorylationStableCapacity.StateHurwitzNonlinearStability

@[expose] public section

namespace PhosphorylationStableCapacity
noncomputable section
open PhosphorylationSharpness

theorem uniformPilotN2J0A_hurwitz : IsHurwitz uniformPilotN2J0A.realMatrix := by
  exact finiteSmallGain_even_hurwitz uniformPilotN2J0A.realMatrix
    uniformPilotN2J0Certificate.complexMatrix (1/8) (1/1000) (1/100) (1/10)
    (by norm_num) uniformPilotN2J0Certificate.complex_charpoly_eq
    uniformPilotN2J0Certificate.row_real uniformPilotN2J0Certificate.column_real
    (by norm_num) (by norm_num) uniformPilotN2J0Certificate.feedback_real (by norm_num)
    uniformPilotN2J0A_constantSign

theorem uniformPilotN2J0actual_linearlyStable :
    IsLinearlyStable 4 2 6 (finiteFixedPrintedRates 1)
      (toCoordinateSpace (chart (finiteFixedPrintedState 1 0))) := by
  intro z hz
  apply uniformPilotN2J0A_hurwitz z
  rw [Matrix.charpoly_map, uniformPilotN2J0A_charpoly_eq_actual, ← Matrix.charpoly_map]
  exact hz

theorem uniformPilotN2J0actual_nonlinearSink :
    IsLocallyAsymptoticallyStableClass 4 2 6 (finiteFixedPrintedRates 1)
      (toCoordinateSpace (chart (finiteFixedPrintedState 1 0))) := by
  have hs := uniformPilotN2J0actualSource
  exact state_linearly_stable_locally_asymptotically_stable
    (by decide) 4 2 6 (by norm_num) (finiteFixedPrintedRates 1)
    hs.1 (finiteFixedPrintedState 1 0) hs.2.1 hs.2.2.1 hs.2.2.2
    uniformPilotN2J0actual_linearlyStable

end
end PhosphorylationStableCapacity
