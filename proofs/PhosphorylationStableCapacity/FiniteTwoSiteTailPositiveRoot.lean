module
public import proofs.PhosphorylationStableCapacity.FiniteTwoSiteTailSimilarityData
public import proofs.PhosphorylationStableCapacity.ScaledIntegerDeterminantSign
public import proofs.PhosphorylationStableCapacity.PositiveRootFromOrientation
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.NormNum

@[expose] public section
set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

namespace PhosphorylationStableCapacity

noncomputable section

open Matrix

def twoSiteTailShiftA0 : ScaledIntegerMatrix (Fin 6) (Fin 6) :=
  ⟨twoSiteTailA0.denominator,
    twoSiteTailA0.entries +
      (2 * (twoSiteTailA0.denominator : ℤ)) • 1⟩

def twoSiteTailShiftA2 : ScaledIntegerMatrix (Fin 6) (Fin 6) :=
  ⟨twoSiteTailA2.denominator,
    twoSiteTailA2.entries +
      (2 * (twoSiteTailA2.denominator : ℤ)) • 1⟩

theorem twoSiteTailShiftA0_real :
    twoSiteTailShiftA0.realMatrix =
      twoSiteTailA0.realMatrix - Matrix.scalar (Fin 6) (-2) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [twoSiteTailShiftA0, twoSiteTailA0,
      ScaledIntegerMatrix.realMatrix, Matrix.sub_apply,
      Matrix.scalar_apply, Matrix.ofNat_apply]

theorem twoSiteTailShiftA2_real :
    twoSiteTailShiftA2.realMatrix =
      twoSiteTailA2.realMatrix - Matrix.scalar (Fin 6) (-2) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [twoSiteTailShiftA2, twoSiteTailA2,
      ScaledIntegerMatrix.realMatrix, Matrix.sub_apply,
      Matrix.scalar_apply, Matrix.ofNat_apply]

private theorem twoSiteTailShiftA0_integer_det_neg :
    twoSiteTailShiftA0.entries.det < 0 := by decide +kernel

private theorem twoSiteTailShiftA2_integer_det_neg :
    twoSiteTailShiftA2.entries.det < 0 := by decide +kernel

theorem twoSiteTailShiftA0_det_neg :
    (twoSiteTailA0.realMatrix - Matrix.scalar (Fin 6) (-2)).det < 0 := by
  rw [← twoSiteTailShiftA0_real, ScaledIntegerMatrix.realMatrix_det]
  have hden : 0 < twoSiteTailShiftA0.denominator := by decide
  exact div_neg_of_neg_of_pos (by exact_mod_cast twoSiteTailShiftA0_integer_det_neg)
    (pow_pos (Nat.cast_pos.mpr hden) _)

theorem twoSiteTailShiftA2_det_neg :
    (twoSiteTailA2.realMatrix - Matrix.scalar (Fin 6) (-2)).det < 0 := by
  rw [← twoSiteTailShiftA2_real, ScaledIntegerMatrix.realMatrix_det]
  have hden : 0 < twoSiteTailShiftA2.denominator := by decide
  exact div_neg_of_neg_of_pos (by exact_mod_cast twoSiteTailShiftA2_integer_det_neg)
    (pow_pos (Nat.cast_pos.mpr hden) _)

/-- Exact negative shifted determinant forces a real characteristic root
strictly to the right of `-2`. -/
theorem twoSiteTailA0_exists_root_above_neg_two :
    ∃ x : ℝ, -2 < x ∧ twoSiteTailA0.realMatrix.charpoly.eval x = 0 := by
  let M := twoSiteTailA0.realMatrix - Matrix.scalar (Fin 6) (-2)
  obtain ⟨y, hy, hroot⟩ := exists_pos_charpoly_root_of_parity_det_neg
    2 (by norm_num) M (by simpa [M] using twoSiteTailShiftA0_det_neg)
  refine ⟨y - 2, by linarith, ?_⟩
  have hshift : M.charpoly =
      twoSiteTailA0.realMatrix.charpoly.comp (Polynomial.X + Polynomial.C (-2)) :=
    Matrix.charpoly_sub_scalar _ _
  rw [hshift] at hroot
  simpa [Polynomial.eval_comp, sub_eq_add_neg] using hroot

theorem twoSiteTailA2_exists_root_above_neg_two :
    ∃ x : ℝ, -2 < x ∧ twoSiteTailA2.realMatrix.charpoly.eval x = 0 := by
  let M := twoSiteTailA2.realMatrix - Matrix.scalar (Fin 6) (-2)
  obtain ⟨y, hy, hroot⟩ := exists_pos_charpoly_root_of_parity_det_neg
    2 (by norm_num) M (by simpa [M] using twoSiteTailShiftA2_det_neg)
  refine ⟨y - 2, by linarith, ?_⟩
  have hshift : M.charpoly =
      twoSiteTailA2.realMatrix.charpoly.comp (Polynomial.X + Polynomial.C (-2)) :=
    Matrix.charpoly_sub_scalar _ _
  rw [hshift] at hroot
  simpa [Polynomial.eval_comp, sub_eq_add_neg] using hroot

end
end PhosphorylationStableCapacity
