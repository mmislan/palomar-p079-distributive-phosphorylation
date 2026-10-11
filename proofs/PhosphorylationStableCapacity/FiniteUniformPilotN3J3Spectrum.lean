module
public import proofs.PhosphorylationStableCapacity.FiniteUniformPilotN3J3Orientation
public import proofs.PhosphorylationStableCapacity.FiniteUniformPilotN3J3Certificate
public import proofs.PhosphorylationStableCapacity.FiniteSmallGainEvenChecker
public import proofs.PhosphorylationStableCapacity.PositiveRootFromOrientation
public import proofs.PhosphorylationStableCapacity.OddSaddleSpectrum
public import proofs.PhosphorylationStableCapacity.StateHurwitzNonlinearStability

@[expose] public section

namespace PhosphorylationStableCapacity
noncomputable section
open PhosphorylationSharpness

theorem uniformPilotN3J3A_oneUnstable :
    ∃ x : ℝ, 0 < x ∧ uniformPilotN3J3A.realMatrix.charpoly.IsRoot x ∧
      ((uniformPilotN3J3A.realMatrix.map (algebraMap ℝ ℂ)).charpoly).derivative.eval (x : ℂ) ≠ 0 ∧
      ∀ z : ℂ, z ∈ spectrum ℂ (uniformPilotN3J3A.realMatrix.map (algebraMap ℝ ℂ)) →
        z.re < 0 ∨ z = (x : ℂ) := by
  have hroot := exists_pos_root_of_monic_eval_zero_neg uniformPilotN3J3A.realMatrix.charpoly
    (Matrix.charpoly_monic _) (by
      rw [← Polynomial.coeff_zero_eq_eval_zero]
      exact uniformPilotN3J3A_constantSign)
  exact one_unstable_spectrum_of_unique_simple_root uniformPilotN3J3A.realMatrix hroot
    uniformPilotN3J3Certificate.unique_right uniformPilotN3J3Certificate.simple_right

theorem uniformPilotN3J3actual_oneUnstableSaddle :
    IsOneUnstableSaddle 8 2 10 (finiteFixedPrintedRates 2)
      (toCoordinateSpace (chart (finiteFixedPrintedState 2 3))) := by
  obtain ⟨x, hx, hr, hd, hspec⟩ := uniformPilotN3J3A_oneUnstable
  have hmap : (uniformPilotN3J3A.realMatrix.map (algebraMap ℝ ℂ)).charpoly =
      ((restrictedJacobianMatrix 8 2 10 (finiteFixedPrintedRates 2) (toCoordinateSpace (chart (finiteFixedPrintedState 2 3)))).map (algebraMap ℝ ℂ)).charpoly := by
    rw [Matrix.charpoly_map, Matrix.charpoly_map, uniformPilotN3J3A_charpoly_eq_actual]
  refine ⟨x, hx, ?_, ?_, ?_⟩
  · rwa [← uniformPilotN3J3A_charpoly_eq_actual]
  · rwa [← hmap]
  · intro z hz
    apply hspec z
    apply Matrix.mem_spectrum_iff_isRoot_charpoly.mpr
    rw [hmap]
    exact Matrix.mem_spectrum_iff_isRoot_charpoly.mp hz

end
end PhosphorylationStableCapacity
