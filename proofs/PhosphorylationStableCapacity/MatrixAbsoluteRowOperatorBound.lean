module
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.Analysis.Normed.Operator.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset

@[expose] public section

namespace PhosphorylationStableCapacity
noncomputable section
open scoped BigOperators
open Matrix

/-- Absolute row sums control the sup norm without a dimension factor. -/
theorem matrix_mulVec_norm_le_of_absolute_rows
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (M : Matrix ι κ ℝ) (B : ℝ) (hB : 0 ≤ B)
    (hrows : ∀ i, (∑ j, |M i j|) ≤ B) (v : κ → ℝ) :
    ‖M *ᵥ v‖ ≤ B*‖v‖ := by
  apply (pi_norm_le_iff_of_nonneg (mul_nonneg hB (norm_nonneg v))).mpr
  intro i
  rw [Real.norm_eq_abs]
  change |∑ j, M i j * v j| ≤ B*‖v‖
  calc
    _ ≤ ∑ j, |M i j * v j| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j, |M i j| * ‖v‖ := by
      apply Finset.sum_le_sum
      intro j hj
      rw [abs_mul]
      apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
      simpa only [Real.norm_eq_abs] using norm_le_pi_norm v j
    _ = (∑ j, |M i j|) * ‖v‖ := (Finset.sum_mul _ _ _).symm
    _ ≤ B*‖v‖ := mul_le_mul_of_nonneg_right (hrows i) (norm_nonneg v)

theorem continuousLinearMap_norm_le_of_absolute_rows
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (A : (κ → ℝ) →L[ℝ] (ι → ℝ)) (M : Matrix ι κ ℝ)
    (hact : ∀ v, A v = M *ᵥ v) (B : ℝ) (hB : 0 ≤ B)
    (hrows : ∀ i, (∑ j, |M i j|) ≤ B) : ‖A‖ ≤ B := by
  apply A.opNorm_le_bound hB
  intro v
  rw [hact]
  exact matrix_mulVec_norm_le_of_absolute_rows M B hB hrows v

end
end PhosphorylationStableCapacity
