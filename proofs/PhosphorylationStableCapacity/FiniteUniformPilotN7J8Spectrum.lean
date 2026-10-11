module
public import proofs.PhosphorylationStableCapacity.FiniteUniformPilotN7J8Orientation
public import proofs.PhosphorylationStableCapacity.FiniteUniformPilotN7J8Certificate
public import proofs.PhosphorylationStableCapacity.FiniteSmallGainEvenChecker
public import proofs.PhosphorylationStableCapacity.PositiveRootFromOrientation
public import proofs.PhosphorylationStableCapacity.OddSaddleSpectrum
public import proofs.PhosphorylationStableCapacity.StateHurwitzNonlinearStability

@[expose] public section

namespace PhosphorylationStableCapacity
noncomputable section
open PhosphorylationSharpness

theorem uniformPilotN7J8A_hurwitz : IsHurwitz uniformPilotN7J8A.realMatrix := by
  exact finiteSmallGain_even_hurwitz uniformPilotN7J8A.realMatrix
    uniformPilotN7J8Certificate.complexMatrix (1/8) (1/1000) (1/100) (1/10)
    (by norm_num) uniformPilotN7J8Certificate.complex_charpoly_eq
    uniformPilotN7J8Certificate.row_real uniformPilotN7J8Certificate.column_real
    (by norm_num) (by norm_num) uniformPilotN7J8Certificate.feedback_real (by norm_num)
    uniformPilotN7J8A_constantSign

theorem uniformPilotN7J8actual_linearlyStable :
    IsLinearlyStable 16 2 18 (finiteFixedPrintedRates 6)
      (toCoordinateSpace (chart (finiteFixedPrintedState 6 8))) := by
  intro z hz
  apply uniformPilotN7J8A_hurwitz z
  rw [Matrix.charpoly_map, uniformPilotN7J8A_charpoly_eq_actual, ← Matrix.charpoly_map]
  exact hz

theorem uniformPilotN7J8actual_nonlinearSink :
    IsLocallyAsymptoticallyStableClass 16 2 18 (finiteFixedPrintedRates 6)
      (toCoordinateSpace (chart (finiteFixedPrintedState 6 8))) := by
  have hs := uniformPilotN7J8actualSource
  exact state_linearly_stable_locally_asymptotically_stable
    (by decide) 16 2 18 (by norm_num) (finiteFixedPrintedRates 6)
    hs.1 (finiteFixedPrintedState 6 8) hs.2.1 hs.2.2.1 hs.2.2.2
    uniformPilotN7J8actual_linearlyStable

end
end PhosphorylationStableCapacity
