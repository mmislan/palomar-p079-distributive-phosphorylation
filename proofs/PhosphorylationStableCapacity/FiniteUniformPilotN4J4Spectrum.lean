module
public import proofs.PhosphorylationStableCapacity.FiniteUniformPilotN4J4Orientation
public import proofs.PhosphorylationStableCapacity.FiniteUniformPilotN4J4Certificate
public import proofs.PhosphorylationStableCapacity.FiniteSmallGainEvenChecker
public import proofs.PhosphorylationStableCapacity.PositiveRootFromOrientation
public import proofs.PhosphorylationStableCapacity.OddSaddleSpectrum
public import proofs.PhosphorylationStableCapacity.StateHurwitzNonlinearStability

@[expose] public section

namespace PhosphorylationStableCapacity
noncomputable section
open PhosphorylationSharpness

theorem uniformPilotN4J4A_hurwitz : IsHurwitz uniformPilotN4J4A.realMatrix := by
  exact finiteSmallGain_even_hurwitz uniformPilotN4J4A.realMatrix
    uniformPilotN4J4Certificate.complexMatrix (1/8) (1/1000) (1/100) (1/10)
    (by norm_num) uniformPilotN4J4Certificate.complex_charpoly_eq
    uniformPilotN4J4Certificate.row_real uniformPilotN4J4Certificate.column_real
    (by norm_num) (by norm_num) uniformPilotN4J4Certificate.feedback_real (by norm_num)
    uniformPilotN4J4A_constantSign

theorem uniformPilotN4J4actual_linearlyStable :
    IsLinearlyStable 8 2 10 (finiteFixedPrintedRates 3)
      (toCoordinateSpace (chart (finiteFixedPrintedState 3 4))) := by
  intro z hz
  apply uniformPilotN4J4A_hurwitz z
  rw [Matrix.charpoly_map, uniformPilotN4J4A_charpoly_eq_actual, ← Matrix.charpoly_map]
  exact hz

theorem uniformPilotN4J4actual_nonlinearSink :
    IsLocallyAsymptoticallyStableClass 8 2 10 (finiteFixedPrintedRates 3)
      (toCoordinateSpace (chart (finiteFixedPrintedState 3 4))) := by
  have hs := uniformPilotN4J4actualSource
  exact state_linearly_stable_locally_asymptotically_stable
    (by decide) 8 2 10 (by norm_num) (finiteFixedPrintedRates 3)
    hs.1 (finiteFixedPrintedState 3 4) hs.2.1 hs.2.2.1 hs.2.2.2
    uniformPilotN4J4actual_linearlyStable

end
end PhosphorylationStableCapacity
