module
public import proofs.PhosphorylationStableCapacity.FiniteUniformPilotN5J2Orientation
public import proofs.PhosphorylationStableCapacity.FiniteUniformPilotN5J2Certificate
public import proofs.PhosphorylationStableCapacity.FiniteSmallGainEvenChecker
public import proofs.PhosphorylationStableCapacity.PositiveRootFromOrientation
public import proofs.PhosphorylationStableCapacity.OddSaddleSpectrum
public import proofs.PhosphorylationStableCapacity.StateHurwitzNonlinearStability

@[expose] public section

namespace PhosphorylationStableCapacity
noncomputable section
open PhosphorylationSharpness

theorem uniformPilotN5J2A_hurwitz : IsHurwitz uniformPilotN5J2A.realMatrix := by
  exact finiteSmallGain_even_hurwitz uniformPilotN5J2A.realMatrix
    uniformPilotN5J2Certificate.complexMatrix (1/8) (1/1000) (1/100) (1/10)
    (by norm_num) uniformPilotN5J2Certificate.complex_charpoly_eq
    uniformPilotN5J2Certificate.row_real uniformPilotN5J2Certificate.column_real
    (by norm_num) (by norm_num) uniformPilotN5J2Certificate.feedback_real (by norm_num)
    uniformPilotN5J2A_constantSign

theorem uniformPilotN5J2actual_linearlyStable :
    IsLinearlyStable 16 2 18 (finiteFixedPrintedRates 4)
      (toCoordinateSpace (chart (finiteFixedPrintedState 4 2))) := by
  intro z hz
  apply uniformPilotN5J2A_hurwitz z
  rw [Matrix.charpoly_map, uniformPilotN5J2A_charpoly_eq_actual, ← Matrix.charpoly_map]
  exact hz

theorem uniformPilotN5J2actual_nonlinearSink :
    IsLocallyAsymptoticallyStableClass 16 2 18 (finiteFixedPrintedRates 4)
      (toCoordinateSpace (chart (finiteFixedPrintedState 4 2))) := by
  have hs := uniformPilotN5J2actualSource
  exact state_linearly_stable_locally_asymptotically_stable
    (by decide) 16 2 18 (by norm_num) (finiteFixedPrintedRates 4)
    hs.1 (finiteFixedPrintedState 4 2) hs.2.1 hs.2.2.1 hs.2.2.2
    uniformPilotN5J2actual_linearlyStable

end
end PhosphorylationStableCapacity
