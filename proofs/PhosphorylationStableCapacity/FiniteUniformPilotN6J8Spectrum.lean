module
public import proofs.PhosphorylationStableCapacity.FiniteUniformPilotN6J8Orientation
public import proofs.PhosphorylationStableCapacity.FiniteUniformPilotN6J8Certificate
public import proofs.PhosphorylationStableCapacity.FiniteSmallGainEvenChecker
public import proofs.PhosphorylationStableCapacity.PositiveRootFromOrientation
public import proofs.PhosphorylationStableCapacity.OddSaddleSpectrum
public import proofs.PhosphorylationStableCapacity.StateHurwitzNonlinearStability

@[expose] public section

namespace PhosphorylationStableCapacity
noncomputable section
open PhosphorylationSharpness

theorem uniformPilotN6J8A_hurwitz : IsHurwitz uniformPilotN6J8A.realMatrix := by
  exact finiteSmallGain_even_hurwitz uniformPilotN6J8A.realMatrix
    uniformPilotN6J8Certificate.complexMatrix (1/8) (1/1000) (1/100) (1/10)
    (by norm_num) uniformPilotN6J8Certificate.complex_charpoly_eq
    uniformPilotN6J8Certificate.row_real uniformPilotN6J8Certificate.column_real
    (by norm_num) (by norm_num) uniformPilotN6J8Certificate.feedback_real (by norm_num)
    uniformPilotN6J8A_constantSign

theorem uniformPilotN6J8actual_linearlyStable :
    IsLinearlyStable 16 2 18 (finiteFixedPrintedRates 5)
      (toCoordinateSpace (chart (finiteFixedPrintedState 5 8))) := by
  intro z hz
  apply uniformPilotN6J8A_hurwitz z
  rw [Matrix.charpoly_map, uniformPilotN6J8A_charpoly_eq_actual, ← Matrix.charpoly_map]
  exact hz

theorem uniformPilotN6J8actual_nonlinearSink :
    IsLocallyAsymptoticallyStableClass 16 2 18 (finiteFixedPrintedRates 5)
      (toCoordinateSpace (chart (finiteFixedPrintedState 5 8))) := by
  have hs := uniformPilotN6J8actualSource
  exact state_linearly_stable_locally_asymptotically_stable
    (by decide) 16 2 18 (by norm_num) (finiteFixedPrintedRates 5)
    hs.1 (finiteFixedPrintedState 5 8) hs.2.1 hs.2.2.1 hs.2.2.2
    uniformPilotN6J8actual_linearlyStable

end
end PhosphorylationStableCapacity
