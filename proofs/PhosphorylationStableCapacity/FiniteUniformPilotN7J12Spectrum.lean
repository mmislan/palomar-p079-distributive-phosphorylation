module
public import proofs.PhosphorylationStableCapacity.FiniteUniformPilotN7J12Orientation
public import proofs.PhosphorylationStableCapacity.FiniteUniformPilotN7J12Certificate
public import proofs.PhosphorylationStableCapacity.FiniteSmallGainEvenChecker
public import proofs.PhosphorylationStableCapacity.PositiveRootFromOrientation
public import proofs.PhosphorylationStableCapacity.OddSaddleSpectrum
public import proofs.PhosphorylationStableCapacity.StateHurwitzNonlinearStability

@[expose] public section

namespace PhosphorylationStableCapacity
noncomputable section
open PhosphorylationSharpness

theorem uniformPilotN7J12A_hurwitz : IsHurwitz uniformPilotN7J12A.realMatrix := by
  exact finiteSmallGain_even_hurwitz uniformPilotN7J12A.realMatrix
    uniformPilotN7J12Certificate.complexMatrix (1/8) (1/1000) (1/100) (1/10)
    (by norm_num) uniformPilotN7J12Certificate.complex_charpoly_eq
    uniformPilotN7J12Certificate.row_real uniformPilotN7J12Certificate.column_real
    (by norm_num) (by norm_num) uniformPilotN7J12Certificate.feedback_real (by norm_num)
    uniformPilotN7J12A_constantSign

theorem uniformPilotN7J12actual_linearlyStable :
    IsLinearlyStable 16 2 18 (finiteFixedPrintedRates 6)
      (toCoordinateSpace (chart (finiteFixedPrintedState 6 12))) := by
  intro z hz
  apply uniformPilotN7J12A_hurwitz z
  rw [Matrix.charpoly_map, uniformPilotN7J12A_charpoly_eq_actual, ← Matrix.charpoly_map]
  exact hz

theorem uniformPilotN7J12actual_nonlinearSink :
    IsLocallyAsymptoticallyStableClass 16 2 18 (finiteFixedPrintedRates 6)
      (toCoordinateSpace (chart (finiteFixedPrintedState 6 12))) := by
  have hs := uniformPilotN7J12actualSource
  exact state_linearly_stable_locally_asymptotically_stable
    (by decide) 16 2 18 (by norm_num) (finiteFixedPrintedRates 6)
    hs.1 (finiteFixedPrintedState 6 12) hs.2.1 hs.2.2.1 hs.2.2.2
    uniformPilotN7J12actual_linearlyStable

end
end PhosphorylationStableCapacity
