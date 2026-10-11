module
public import proofs.PhosphorylationStableCapacity.FiniteUniformPilotN4J0Orientation
public import proofs.PhosphorylationStableCapacity.FiniteUniformPilotN4J0Certificate
public import proofs.PhosphorylationStableCapacity.FiniteSmallGainEvenChecker
public import proofs.PhosphorylationStableCapacity.PositiveRootFromOrientation
public import proofs.PhosphorylationStableCapacity.OddSaddleSpectrum
public import proofs.PhosphorylationStableCapacity.StateHurwitzNonlinearStability

@[expose] public section

namespace PhosphorylationStableCapacity
noncomputable section
open PhosphorylationSharpness

theorem uniformPilotN4J0A_hurwitz : IsHurwitz uniformPilotN4J0A.realMatrix := by
  exact finiteSmallGain_even_hurwitz uniformPilotN4J0A.realMatrix
    uniformPilotN4J0Certificate.complexMatrix (1/8) (1/1000) (1/100) (1/10)
    (by norm_num) uniformPilotN4J0Certificate.complex_charpoly_eq
    uniformPilotN4J0Certificate.row_real uniformPilotN4J0Certificate.column_real
    (by norm_num) (by norm_num) uniformPilotN4J0Certificate.feedback_real (by norm_num)
    uniformPilotN4J0A_constantSign

theorem uniformPilotN4J0actual_linearlyStable :
    IsLinearlyStable 8 2 10 (finiteFixedPrintedRates 3)
      (toCoordinateSpace (chart (finiteFixedPrintedState 3 0))) := by
  intro z hz
  apply uniformPilotN4J0A_hurwitz z
  rw [Matrix.charpoly_map, uniformPilotN4J0A_charpoly_eq_actual, ← Matrix.charpoly_map]
  exact hz

theorem uniformPilotN4J0actual_nonlinearSink :
    IsLocallyAsymptoticallyStableClass 8 2 10 (finiteFixedPrintedRates 3)
      (toCoordinateSpace (chart (finiteFixedPrintedState 3 0))) := by
  have hs := uniformPilotN4J0actualSource
  exact state_linearly_stable_locally_asymptotically_stable
    (by decide) 8 2 10 (by norm_num) (finiteFixedPrintedRates 3)
    hs.1 (finiteFixedPrintedState 3 0) hs.2.1 hs.2.2.1 hs.2.2.2
    uniformPilotN4J0actual_linearlyStable

end
end PhosphorylationStableCapacity
