module
public import Mathlib.LinearAlgebra.Matrix.SchurComplement
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.Ring

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section
open Matrix

/-- The free-species covariance and the complex affinity Hessian have
complementary determinants. This retains the magnitude in the binding
elimination, rather than only its positive orientation. -/
theorem complementary_binding_determinant
    {f c : Type*} [Fintype f] [Fintype c]
    [DecidableEq f] [DecidableEq c]
    (Df : Matrix f f ℝ) (Dc : Matrix c c ℝ)
    (K : Matrix f c ℝ) (hf : IsUnit Df.det) (hc : IsUnit Dc.det) :
    (Dc⁻¹ + K.transpose * Df⁻¹ * K).det * Df.det * Dc.det =
      (Df + K * Dc * K.transpose).det := by
  let _ : Invertible Df := invertibleOfIsUnitDet Df hf
  let _ : Invertible Dc⁻¹ :=
    invertibleOfIsUnitDet Dc⁻¹ (by
      rw [det_nonsing_inv, Ring.inverse_eq_inv]; exact hc.inv)
  have htop := det_fromBlocks₁₁ Df K (-K.transpose) Dc⁻¹
  have hbottom := det_fromBlocks₂₂ Df K (-K.transpose) Dc⁻¹
  rw [invOf_eq_nonsing_inv, Matrix.neg_mul, Matrix.neg_mul, sub_neg_eq_add] at htop
  rw [invOf_eq_nonsing_inv, nonsing_inv_nonsing_inv _ hc,
    Matrix.mul_neg, sub_neg_eq_add, det_nonsing_inv,
    Ring.inverse_eq_inv] at hbottom
  have h := htop.symm.trans hbottom
  have hdc : Dc.det ≠ 0 := hc.ne_zero
  calc
    (Dc⁻¹ + K.transpose * Df⁻¹ * K).det * Df.det * Dc.det =
        (Df.det * (Dc⁻¹ + K.transpose * Df⁻¹ * K).det) * Dc.det := by ring
    _ = (Dc.det⁻¹ * (Df + K * Dc * K.transpose).det) * Dc.det := by rw [h]
    _ = (Df + K * Dc * K.transpose).det := by
      rw [mul_assoc, mul_comm _ Dc.det, ← mul_assoc, inv_mul_cancel₀ hdc, one_mul]

/-- Eliminating the two enzyme inventories gives the literal loaded
mass correction, with its exact enzyme-total determinant factor. -/
theorem enzyme_corrected_covariance_determinant
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (S C Y : ι → ℝ) (ET FT : ℝ) (hET : ET ≠ 0) (hFT : FT ≠ 0) :
    let U : Matrix ι (Fin 2) ℝ := fun i => ![C i, Y i]
    let L := diagonal (fun i => S i + C i + Y i)
    let G := diagonal ![ET, FT]
    (fromBlocks L U U.transpose G).det =
      ET * FT *
        Matrix.det (fun i j => (if i = j then S i + C i + Y i else 0) -
          C i * C j / ET - Y i * Y j / FT) := by
  dsimp only
  let U : Matrix ι (Fin 2) ℝ := fun i => ![C i, Y i]
  let L : Matrix ι ι ℝ := diagonal (fun i => S i + C i + Y i)
  let G : Matrix (Fin 2) (Fin 2) ℝ := diagonal ![ET, FT]
  have hG : IsUnit G.det := by
    rw [isUnit_iff_ne_zero]
    simpa [G, det_fin_two, diagonal_apply] using mul_ne_zero hET hFT
  let _ : Invertible G := invertibleOfIsUnitDet G hG
  have hdet := det_fromBlocks₂₂ L U U.transpose G
  have hginv : G⁻¹ = diagonal ![ET⁻¹, FT⁻¹] := by
    apply inv_eq_right_inv
    change diagonal ![ET, FT] * diagonal ![ET⁻¹, FT⁻¹] = 1
    rw [diagonal_mul_diagonal]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [mul_inv_cancel₀ hET, mul_inv_cancel₀ hFT]
  have hentry : L - U * G⁻¹ * U.transpose =
      fun i j => (if i = j then S i + C i + Y i else 0) -
        C i * C j / ET - Y i * Y j / FT := by
    ext i j
    rw [hginv]
    simp only [Matrix.sub_apply, Matrix.mul_apply]
    dsimp only [Matrix.transpose]
    simp [L, U, Fin.sum_univ_two, Matrix.diagonal_apply,
      div_eq_mul_inv]
    ring
  rw [invOf_eq_nonsing_inv, hentry] at hdet
  simpa [G, det_fin_two, diagonal_apply] using hdet

end
end PhosphorylationStableCapacity
