module
public import proofs.PhosphorylationStableCapacity.FastSlowNearZero

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section

open Matrix

/-- The block pencil obtained by multiplying the fast rows of the
full characteristic matrix by the binding time scale. -/
def fastSlowCharacteristicBlock {s f : Type*} [Fintype s] [Fintype f]
    [DecidableEq s] [DecidableEq f]
    (A : Matrix s s ℂ) (B : Matrix s f ℂ)
    (C : Matrix f s ℂ) (D : Matrix f f ℂ)
    (ε z : ℂ) : Matrix (s ⊕ f) (s ⊕ f) ℂ :=
  Matrix.fromBlocks (z • 1 - A) (-B) (-C) ((ε * z) • 1 - D)

/-- At zero binding time scale, the block-pencil determinant is the
ordinary Schur characteristic determinant times the fast determinant. -/
theorem fastSlowCharacteristicBlock_det_zero
    {s f : Type*} [Fintype s] [Fintype f]
    [DecidableEq s] [DecidableEq f]
    (A : Matrix s s ℂ) (B : Matrix s f ℂ)
    (C : Matrix f s ℂ) (D : Matrix f f ℂ)
    (hD : ∀ w : ℂ, w ∈ spectrum ℂ D → w.re < 0)
    (z : ℂ) :
    (fastSlowCharacteristicBlock A B C D 0 z).det =
      (-D).det * (z • 1 - (A - B * D⁻¹ * C)).det := by
  have hunit : IsUnit (-D).det := by
    simpa [fastSlowResolventMatrix] using
      (fastSlowResolventMatrix_isUnit_det_of_hurwitz D hD
        (show (0 : ℝ) < 1 by norm_num) 0 (le_refl 0))
  have hDunit : IsUnit D.det := by
    have hnegMatrix : IsUnit (-D) :=
      (Matrix.isUnit_iff_isUnit_det (-D)).mpr hunit
    have hDMatrix : IsUnit D := by simpa using hnegMatrix.neg
    exact (Matrix.isUnit_iff_isUnit_det D).mp hDMatrix
  have hInvertibleD : Invertible D := Matrix.invertibleOfIsUnitDet D hDunit
  have hInvertibleNegD : Invertible (-D) := Matrix.invertibleOfIsUnitDet (-D) hunit
  simp only [fastSlowCharacteristicBlock, zero_mul, zero_smul, zero_sub,
    Matrix.det_fromBlocks₂₂]
  congr 1
  rw [invOf_neg, invOf_eq_nonsing_inv]
  congr 1
  simp only [Matrix.neg_mul, Matrix.mul_neg, neg_neg, sub_neg_eq_add]
  abel

end
end PhosphorylationStableCapacity
