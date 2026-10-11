module
public import proofs.PhosphorylationStableCapacity.HurwitzNonsingular

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section

/-- The constant coefficient of a Hurwitz matrix's characteristic
polynomial is nonzero, so an added factor `X` represents an algebraically
simple zero. -/
theorem isHurwitz_charpoly_eval_zero_ne_zero
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : Matrix ι ι ℝ} (hA : IsHurwitz A) :
    A.charpoly.eval 0 ≠ 0 := by
  intro hzero
  have hnegdet : (-A).det = 0 := by
    rw [Matrix.eval_charpoly] at hzero
    simpa using hzero
  have hproduct : (-1 : ℝ) ^ Fintype.card ι * A.det = 0 := by
    simpa only [Matrix.det_neg] using hnegdet
  have hdet : A.det = 0 :=
    (mul_eq_zero.mp hproduct).resolve_left (by simp)
  exact (isHurwitz_det_ne_zero hA) hdet

end
end PhosphorylationStableCapacity
