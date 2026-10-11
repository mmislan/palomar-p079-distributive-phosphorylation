module
public import proofs.PhosphorylationStableCapacity.ScaledIntegerMatrixCertificates
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section

theorem ScaledIntegerMatrix.realMatrix_det
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : ScaledIntegerMatrix ι ι) :
    A.realMatrix.det =
      (A.entries.det : ℝ) / (A.denominator : ℝ) ^ Fintype.card ι := by
  rw [ScaledIntegerMatrix.realMatrix, Matrix.det_smul]
  change (A.denominator : ℝ)⁻¹ ^ Fintype.card ι *
    (A.entries.map (fun x => (x : ℝ))).det = _
  rw [← Int.cast_det]
  simp only [div_eq_mul_inv, inv_pow]
  ring

theorem ScaledIntegerMatrix.realMatrix_det_pos
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : ScaledIntegerMatrix ι ι)
    (hden : 0 < A.denominator) (hdet : 0 < A.entries.det) :
    0 < A.realMatrix.det := by
  rw [A.realMatrix_det]
  exact div_pos (by exact_mod_cast hdet)
    (pow_pos (by exact_mod_cast hden) _)

end
end PhosphorylationStableCapacity
