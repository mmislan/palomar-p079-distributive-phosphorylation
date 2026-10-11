module
public import proofs.PhosphorylationStableCapacity.FiniteUniformPilotN3J2Orientation
public import proofs.PhosphorylationStableCapacity.FiniteUniformPilotN3J2Certificate
public import proofs.PhosphorylationStableCapacity.FiniteSmallGainEvenChecker
public import proofs.PhosphorylationStableCapacity.PositiveRootFromOrientation
public import proofs.PhosphorylationStableCapacity.OddSaddleSpectrum
public import proofs.PhosphorylationStableCapacity.StateHurwitzNonlinearStability

@[expose] public section

namespace PhosphorylationStableCapacity
noncomputable section
open PhosphorylationSharpness

theorem uniformPilotN3J2A_hurwitz : IsHurwitz uniformPilotN3J2A.realMatrix := by
  exact finiteSmallGain_even_hurwitz uniformPilotN3J2A.realMatrix
    uniformPilotN3J2Certificate.complexMatrix (1/8) (1/1000) (1/100) (1/10)
    (by norm_num) uniformPilotN3J2Certificate.complex_charpoly_eq
    uniformPilotN3J2Certificate.row_real uniformPilotN3J2Certificate.column_real
    (by norm_num) (by norm_num) uniformPilotN3J2Certificate.feedback_real (by norm_num)
    uniformPilotN3J2A_constantSign

theorem uniformPilotN3J2actual_linearlyStable :
    IsLinearlyStable 8 2 10 (finiteFixedPrintedRates 2)
      (toCoordinateSpace (chart (finiteFixedPrintedState 2 2))) := by
  intro z hz
  apply uniformPilotN3J2A_hurwitz z
  rw [Matrix.charpoly_map, uniformPilotN3J2A_charpoly_eq_actual, ← Matrix.charpoly_map]
  exact hz

theorem uniformPilotN3J2actual_nonlinearSink :
    IsLocallyAsymptoticallyStableClass 8 2 10 (finiteFixedPrintedRates 2)
      (toCoordinateSpace (chart (finiteFixedPrintedState 2 2))) := by
  have hs := uniformPilotN3J2actualSource
  exact state_linearly_stable_locally_asymptotically_stable
    (by decide) 8 2 10 (by norm_num) (finiteFixedPrintedRates 2)
    hs.1 (finiteFixedPrintedState 2 2) hs.2.1 hs.2.2.1 hs.2.2.2
    uniformPilotN3J2actual_linearlyStable

end
end PhosphorylationStableCapacity
