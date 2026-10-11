module
public import proofs.PhosphorylationStableCapacity.SourceAugmentedRankOne
public import proofs.PhosphorylationStableCapacity.SourceAffineCurrentAction

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section
open PhosphorylationSharpness Matrix

/-- The loaded total's affine log-substrate action is exactly the
zeroth/first-moment expression in the augmented determinant. -/
theorem sourceAugmentedTotalRow_affine_action {n : ℕ}
    (x : State n) (a b : ℝ) :
    sourceAugmentedTotalRow x ⬝ᵥ sourceAffineLogTangent a b =
      a * sourcePathZerothMoment (sourceAugmentedTotalRow x) +
        b * sourcePathFirstMoment (sourceAugmentedTotalRow x) := by
  simp only [dotProduct, sourceAffineLogTangent, mul_add,
    Finset.sum_add_distrib, sourcePathZerothMoment,
    sourcePathFirstMoment]
  rw [Finset.mul_sum, Finset.mul_sum]
  apply congrArg₂ (· + ·)
  · apply Finset.sum_congr rfl
    intro j _
    ring
  · apply Finset.sum_congr rfl
    intro j _
    ring

theorem sourceOccupancyFirstMoment_eq_path {n : ℕ}
    (x : State n) :
    sourceOccupancyFirstMoment x =
      sourcePathFirstMoment (sourceOccupancyDifference x) := rfl

/-- An affine log-substrate tangent whose literal current derivative
vanishes and whose loaded total decreases has stable orientation. -/
theorem sourceAugmentedCurrentMatrix_parity_det_pos_of_affine_tangent
    {n : ℕ} (k : Rates n) (x : State n)
    (hk : k.Positive) (hx : x.Positive)
    (a b : ℝ) (hb : 0 < b)
    (hq : sourcePathZerothMoment (sourceOccupancyDifference x) < 0)
    (hcurrent : a * (∑ j : Fin (n+1), sourceOccupancyDifference x j) +
      b * (sourceOccupancyFirstMoment x - 1) = 0)
    (htotal : sourceAugmentedTotalRow x ⬝ᵥ
      sourceAffineLogTangent a b < 0) :
    0 < (-1 : ℝ)^n * (sourceAugmentedCurrentMatrix k x).det := by
  apply sourceAugmentedCurrentMatrix_parity_det_pos_of_affine_slope_neg
    k x hk hx a b hb hq
  · simpa only [sourcePathZerothMoment,
      sourceOccupancyFirstMoment_eq_path] using hcurrent
  · simpa only [sourceAugmentedTotalRow_affine_action] using htotal

end
end PhosphorylationStableCapacity
