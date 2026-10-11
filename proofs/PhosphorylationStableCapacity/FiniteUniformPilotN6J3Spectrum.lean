module
public import proofs.PhosphorylationStableCapacity.FiniteUniformPilotN6J3Orientation
public import proofs.PhosphorylationStableCapacity.FiniteUniformPilotN6J3Certificate
public import proofs.PhosphorylationStableCapacity.FiniteSmallGainEvenChecker
public import proofs.PhosphorylationStableCapacity.PositiveRootFromOrientation
public import proofs.PhosphorylationStableCapacity.OddSaddleSpectrum
public import proofs.PhosphorylationStableCapacity.StateHurwitzNonlinearStability

@[expose] public section

namespace PhosphorylationStableCapacity
noncomputable section
open PhosphorylationSharpness

theorem uniformPilotN6J3A_oneUnstable :
    ∃ x : ℝ, 0 < x ∧ uniformPilotN6J3A.realMatrix.charpoly.IsRoot x ∧
      ((uniformPilotN6J3A.realMatrix.map (algebraMap ℝ ℂ)).charpoly).derivative.eval (x : ℂ) ≠ 0 ∧
      ∀ z : ℂ, z ∈ spectrum ℂ (uniformPilotN6J3A.realMatrix.map (algebraMap ℝ ℂ)) →
        z.re < 0 ∨ z = (x : ℂ) := by
  have hroot := exists_pos_root_of_monic_eval_zero_neg uniformPilotN6J3A.realMatrix.charpoly
    (Matrix.charpoly_monic _) (by
      rw [← Polynomial.coeff_zero_eq_eval_zero]
      exact uniformPilotN6J3A_constantSign)
  exact one_unstable_spectrum_of_unique_simple_root uniformPilotN6J3A.realMatrix hroot
    uniformPilotN6J3Certificate.unique_right uniformPilotN6J3Certificate.simple_right

theorem uniformPilotN6J3actual_oneUnstableSaddle :
    IsOneUnstableSaddle 16 2 18 (finiteFixedPrintedRates 5)
      (toCoordinateSpace (chart (finiteFixedPrintedState 5 3))) := by
  obtain ⟨x, hx, hr, hd, hspec⟩ := uniformPilotN6J3A_oneUnstable
  have hmap : (uniformPilotN6J3A.realMatrix.map (algebraMap ℝ ℂ)).charpoly =
      ((restrictedJacobianMatrix 16 2 18 (finiteFixedPrintedRates 5) (toCoordinateSpace (chart (finiteFixedPrintedState 5 3)))).map (algebraMap ℝ ℂ)).charpoly := by
    rw [Matrix.charpoly_map, Matrix.charpoly_map, uniformPilotN6J3A_charpoly_eq_actual]
  refine ⟨x, hx, ?_, ?_, ?_⟩
  · rwa [← uniformPilotN6J3A_charpoly_eq_actual]
  · rwa [← hmap]
  · intro z hz
    apply hspec z
    apply Matrix.mem_spectrum_iff_isRoot_charpoly.mpr
    rw [hmap]
    exact Matrix.mem_spectrum_iff_isRoot_charpoly.mp hz

end
end PhosphorylationStableCapacity
