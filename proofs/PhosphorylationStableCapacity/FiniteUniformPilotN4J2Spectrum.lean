module
public import proofs.PhosphorylationStableCapacity.FiniteUniformPilotN4J2Orientation
public import proofs.PhosphorylationStableCapacity.FiniteUniformPilotN4J2Certificate
public import proofs.PhosphorylationStableCapacity.FiniteSmallGainEvenChecker
public import proofs.PhosphorylationStableCapacity.PositiveRootFromOrientation
public import proofs.PhosphorylationStableCapacity.OddSaddleSpectrum
public import proofs.PhosphorylationStableCapacity.StateHurwitzNonlinearStability

@[expose] public section

namespace PhosphorylationStableCapacity
noncomputable section
open PhosphorylationSharpness

theorem uniformPilotN4J2A_hurwitz : IsHurwitz uniformPilotN4J2A.realMatrix := by
  exact finiteSmallGain_even_hurwitz uniformPilotN4J2A.realMatrix
    uniformPilotN4J2Certificate.complexMatrix (1/8) (1/1000) (1/100) (1/10)
    (by norm_num) uniformPilotN4J2Certificate.complex_charpoly_eq
    uniformPilotN4J2Certificate.row_real uniformPilotN4J2Certificate.column_real
    (by norm_num) (by norm_num) uniformPilotN4J2Certificate.feedback_real (by norm_num)
    uniformPilotN4J2A_constantSign

theorem uniformPilotN4J2actual_linearlyStable :
    IsLinearlyStable 8 2 10 (finiteFixedPrintedRates 3)
      (toCoordinateSpace (chart (finiteFixedPrintedState 3 2))) := by
  intro z hz
  apply uniformPilotN4J2A_hurwitz z
  rw [Matrix.charpoly_map, uniformPilotN4J2A_charpoly_eq_actual, ← Matrix.charpoly_map]
  exact hz

theorem uniformPilotN4J2actual_nonlinearSink :
    IsLocallyAsymptoticallyStableClass 8 2 10 (finiteFixedPrintedRates 3)
      (toCoordinateSpace (chart (finiteFixedPrintedState 3 2))) := by
  have hs := uniformPilotN4J2actualSource
  exact state_linearly_stable_locally_asymptotically_stable
    (by decide) 8 2 10 (by norm_num) (finiteFixedPrintedRates 3)
    hs.1 (finiteFixedPrintedState 3 2) hs.2.1 hs.2.2.1 hs.2.2.2
    uniformPilotN4J2actual_linearlyStable

end
end PhosphorylationStableCapacity
