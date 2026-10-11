module
public import Mathlib.LinearAlgebra.Matrix.SchurComplement
public import proofs.PhosphorylationStableCapacity.AugmentedDifferenceDeterminant

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section
open Matrix

/-- Common occupancy row added to every path-difference current row. -/
def sourceRankOneAugmented {n : ℕ}
    (t q : Fin (n+1) → ℝ) :
    Matrix (Fin (n+1)) (Fin (n+1)) ℝ :=
  sourceDifferenceAugmented t +
    Matrix.replicateCol Unit sourcePathUnitVector *
      Matrix.replicateRow Unit q

theorem sourceRankOneAugmented_apply {n : ℕ}
    (t q : Fin (n+1) → ℝ) (i j : Fin (n+1)) :
    sourceRankOneAugmented t q i j =
      sourceDifferenceAugmented t i j + sourcePathUnitVector i * q j := by
  simp [sourceRankOneAugmented, Matrix.mul_apply,
    Matrix.replicateCol_apply, Matrix.replicateRow_apply]

theorem sourceRankOneAugmented_first_row {n : ℕ}
    (t q : Fin (n+1) → ℝ) (j : Fin (n+1)) :
    sourceRankOneAugmented t q 0 j = t j := by
  rw [sourceRankOneAugmented_apply]
  simp [sourceDifferenceAugmented, sourcePathUnitVector]

theorem sourceRankOneAugmented_current_row {n : ℕ}
    (t q : Fin (n+1) → ℝ) (i : Fin n) (j : Fin (n+1)) :
    sourceRankOneAugmented t q i.succ j =
      (if j = i.castSucc then 1 else 0) -
        (if j = i.succ then 1 else 0) + q j := by
  rw [sourceRankOneAugmented_apply]
  simp [sourceDifferenceAugmented, sourcePathUnitVector]

theorem sourceDifferenceSolution_dot {n : ℕ}
    (t q : Fin (n+1) → ℝ) :
    q ⬝ᵥ sourceDifferenceSolution t =
      sourcePathZerothMoment q *
          (sourcePathFirstMoment t / sourcePathZerothMoment t) -
        sourcePathFirstMoment q := by
  simp only [dotProduct, sourceDifferenceSolution,
    sourcePathZerothMoment, sourcePathFirstMoment]
  simp only [mul_sub, Finset.sum_sub_distrib,
    ← Finset.sum_mul]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- The exact all-size rank-one current determinant. The positive
total-row sum is the pivot that makes the base path matrix invertible. -/
theorem sourceRankOneAugmented_det {n : ℕ}
    (t q : Fin (n+1) → ℝ)
    (h0 : sourcePathZerothMoment t ≠ 0) :
    (sourceRankOneAugmented t q).det =
      (-1 : ℝ)^n *
        ((1 - sourcePathFirstMoment q) * sourcePathZerothMoment t +
          sourcePathZerothMoment q * sourcePathFirstMoment t) := by
  let M := sourceDifferenceAugmented t
  have hMdet : M.det = (-1 : ℝ)^n * sourcePathZerothMoment t := by
    simpa only [M, sourcePathZerothMoment] using
      sourceDifferenceAugmented_det t
  have hMne : M.det ≠ 0 := by
    rw [hMdet]
    exact mul_ne_zero (pow_ne_zero _ (by norm_num)) h0
  have hunit : IsUnit M.det := isUnit_iff_ne_zero.mpr hMne
  have hInvertible : Invertible M :=
    Matrix.invertibleOfIsUnitDet M hunit
  have hinv : M⁻¹.mulVec sourcePathUnitVector =
      sourceDifferenceSolution t := by
    exact @Matrix.inv_mulVec_eq_vec (Fin (n+1)) ℝ
      inferInstance inferInstance inferInstance M hInvertible
      sourcePathUnitVector (sourceDifferenceSolution t)
      ((sourceDifferenceAugmented_solution t h0).symm)
  rw [sourceRankOneAugmented,
    Matrix.det_add_replicateCol_mul_replicateRow hunit]
  rw [Matrix.mul_assoc]
  simp only [Matrix.det_unique, Matrix.add_apply,
    Matrix.one_apply_eq, Matrix.mul_apply,
    Matrix.replicateRow_apply, Matrix.replicateCol_apply]
  have hsum :
      (∑ x : Fin (n+1), q x *
          ∑ y : Fin (n+1), M⁻¹ x y * sourcePathUnitVector y) =
        q ⬝ᵥ sourceDifferenceSolution t := by
    simp only [dotProduct]
    apply Finset.sum_congr rfl
    intro x _
    congr 1
    simpa only [Matrix.mulVec, dotProduct] using congrFun hinv x
  rw [hsum]
  rw [hMdet, sourceDifferenceSolution_dot]
  field_simp [h0]
  ring

end
end PhosphorylationStableCapacity
