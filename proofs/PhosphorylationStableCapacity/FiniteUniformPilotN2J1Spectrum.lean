module
public import proofs.PhosphorylationStableCapacity.FiniteUniformPilotN2J1Orientation
public import proofs.PhosphorylationStableCapacity.FiniteUniformPilotN2J1Certificate
public import proofs.PhosphorylationStableCapacity.FiniteSmallGainEvenChecker
public import proofs.PhosphorylationStableCapacity.PositiveRootFromOrientation
public import proofs.PhosphorylationStableCapacity.OddSaddleSpectrum
public import proofs.PhosphorylationStableCapacity.StateHurwitzNonlinearStability

@[expose] public section

namespace PhosphorylationStableCapacity
noncomputable section
open PhosphorylationSharpness

theorem uniformPilotN2J1A_oneUnstable :
    ∃ x : ℝ, 0 < x ∧ uniformPilotN2J1A.realMatrix.charpoly.IsRoot x ∧
      ((uniformPilotN2J1A.realMatrix.map (algebraMap ℝ ℂ)).charpoly).derivative.eval (x : ℂ) ≠ 0 ∧
      ∀ z : ℂ, z ∈ spectrum ℂ (uniformPilotN2J1A.realMatrix.map (algebraMap ℝ ℂ)) →
        z.re < 0 ∨ z = (x : ℂ) := by
  have hroot := exists_pos_root_of_monic_eval_zero_neg uniformPilotN2J1A.realMatrix.charpoly
    (Matrix.charpoly_monic _) (by
      rw [← Polynomial.coeff_zero_eq_eval_zero]
      exact uniformPilotN2J1A_constantSign)
  exact one_unstable_spectrum_of_unique_simple_root uniformPilotN2J1A.realMatrix hroot
    uniformPilotN2J1Certificate.unique_right uniformPilotN2J1Certificate.simple_right

theorem uniformPilotN2J1actual_oneUnstableSaddle :
    IsOneUnstableSaddle 4 2 6 (finiteFixedPrintedRates 1)
      (toCoordinateSpace (chart (finiteFixedPrintedState 1 1))) := by
  obtain ⟨x, hx, hr, hd, hspec⟩ := uniformPilotN2J1A_oneUnstable
  have hmap : (uniformPilotN2J1A.realMatrix.map (algebraMap ℝ ℂ)).charpoly =
      ((restrictedJacobianMatrix 4 2 6 (finiteFixedPrintedRates 1) (toCoordinateSpace (chart (finiteFixedPrintedState 1 1)))).map (algebraMap ℝ ℂ)).charpoly := by
    rw [Matrix.charpoly_map, Matrix.charpoly_map, uniformPilotN2J1A_charpoly_eq_actual]
  refine ⟨x, hx, ?_, ?_, ?_⟩
  · rwa [← uniformPilotN2J1A_charpoly_eq_actual]
  · rwa [← hmap]
  · intro z hz
    apply hspec z
    apply Matrix.mem_spectrum_iff_isRoot_charpoly.mpr
    rw [hmap]
    exact Matrix.mem_spectrum_iff_isRoot_charpoly.mp hz

end
end PhosphorylationStableCapacity
