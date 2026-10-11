module
public import proofs.PhosphorylationStableCapacity.FiniteUniformPilotN5J5Orientation
public import proofs.PhosphorylationStableCapacity.FiniteUniformPilotN5J5Certificate
public import proofs.PhosphorylationStableCapacity.FiniteSmallGainEvenChecker
public import proofs.PhosphorylationStableCapacity.PositiveRootFromOrientation
public import proofs.PhosphorylationStableCapacity.OddSaddleSpectrum
public import proofs.PhosphorylationStableCapacity.StateHurwitzNonlinearStability

@[expose] public section

namespace PhosphorylationStableCapacity
noncomputable section
open PhosphorylationSharpness

theorem uniformPilotN5J5A_oneUnstable :
    ∃ x : ℝ, 0 < x ∧ uniformPilotN5J5A.realMatrix.charpoly.IsRoot x ∧
      ((uniformPilotN5J5A.realMatrix.map (algebraMap ℝ ℂ)).charpoly).derivative.eval (x : ℂ) ≠ 0 ∧
      ∀ z : ℂ, z ∈ spectrum ℂ (uniformPilotN5J5A.realMatrix.map (algebraMap ℝ ℂ)) →
        z.re < 0 ∨ z = (x : ℂ) := by
  have hroot := exists_pos_root_of_monic_eval_zero_neg uniformPilotN5J5A.realMatrix.charpoly
    (Matrix.charpoly_monic _) (by
      rw [← Polynomial.coeff_zero_eq_eval_zero]
      exact uniformPilotN5J5A_constantSign)
  exact one_unstable_spectrum_of_unique_simple_root uniformPilotN5J5A.realMatrix hroot
    uniformPilotN5J5Certificate.unique_right uniformPilotN5J5Certificate.simple_right

theorem uniformPilotN5J5actual_oneUnstableSaddle :
    IsOneUnstableSaddle 16 2 18 (finiteFixedPrintedRates 4)
      (toCoordinateSpace (chart (finiteFixedPrintedState 4 5))) := by
  obtain ⟨x, hx, hr, hd, hspec⟩ := uniformPilotN5J5A_oneUnstable
  have hmap : (uniformPilotN5J5A.realMatrix.map (algebraMap ℝ ℂ)).charpoly =
      ((restrictedJacobianMatrix 16 2 18 (finiteFixedPrintedRates 4) (toCoordinateSpace (chart (finiteFixedPrintedState 4 5)))).map (algebraMap ℝ ℂ)).charpoly := by
    rw [Matrix.charpoly_map, Matrix.charpoly_map, uniformPilotN5J5A_charpoly_eq_actual]
  refine ⟨x, hx, ?_, ?_, ?_⟩
  · rwa [← uniformPilotN5J5A_charpoly_eq_actual]
  · rwa [← hmap]
  · intro z hz
    apply hspec z
    apply Matrix.mem_spectrum_iff_isRoot_charpoly.mpr
    rw [hmap]
    exact Matrix.mem_spectrum_iff_isRoot_charpoly.mp hz

end
end PhosphorylationStableCapacity
