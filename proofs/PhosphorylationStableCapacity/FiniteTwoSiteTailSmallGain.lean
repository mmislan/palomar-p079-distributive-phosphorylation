module
public import proofs.PhosphorylationStableCapacity.FiniteTwoSiteTailSimilarityData
public import proofs.PhosphorylationStableCapacity.SaddleSmallGainMatrix
public import proofs.PhosphorylationStableCapacity.SaddleSmallGainSimpleSpectrum
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.NormNum

@[expose] public section
set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

namespace PhosphorylationStableCapacity

noncomputable section

private theorem shifted_root_of_root (M : Matrix (Fin 6) (Fin 6) ℂ)
    (z : ℂ) (hz : M.charpoly.eval z = 0) :
    (M - Matrix.scalar (Fin 6) (-2) : Matrix (Fin 6) (Fin 6) ℂ).charpoly.eval (z + 2) = 0 := by
  rw [Matrix.charpoly_sub_scalar]
  simpa [Polynomial.eval_comp] using hz

private theorem unique_above_neg_two_of_shifted_bounds
    (M : Matrix (Fin 6) (Fin 6) ℂ)
    (hrow : ∀ i : Fin 5,
      ((M - Matrix.scalar (Fin 6) (-2) : Matrix (Fin 6) (Fin 6) ℂ) i.succ i.succ).re +
        ∑ j ∈ (Finset.univ : Finset (Fin 5)).erase i,
          ‖(M - Matrix.scalar (Fin 6) (-2) : Matrix (Fin 6) (Fin 6) ℂ) i.succ j.succ‖ ≤
            -(1 / 4 : ℝ))
    (hcol : ∀ i : Fin 5,
      ‖(M - Matrix.scalar (Fin 6) (-2) : Matrix (Fin 6) (Fin 6) ℂ) i.succ 0‖ ≤ (1 / 500 : ℝ))
    (hfeedback :
      (∑ i : Fin 5,
        ‖(M - Matrix.scalar (Fin 6) (-2) : Matrix (Fin 6) (Fin 6) ℂ) 0 i.succ‖) ≤
          (1 / 300 : ℝ))
    (z z' : ℂ) (hz : -2 ≤ z.re) (hz' : -2 ≤ z'.re)
    (hroot : M.charpoly.eval z = 0)
    (hroot' : M.charpoly.eval z' = 0) : z = z' := by
  have h := block_spectrum_unique_right
    (M - Matrix.scalar (Fin 6) (-2) : Matrix (Fin 6) (Fin 6) ℂ)
    (1 / 4) (1 / 500) (1 / 100) (1 / 300)
    (by norm_num) hrow hcol (by norm_num) (by norm_num)
    hfeedback (by norm_num)
    (z + 2) (z' + 2)
    (by simp; linarith) (by simp; linarith)
    (shifted_root_of_root M z hroot)
    (shifted_root_of_root M z' hroot')
  exact add_right_cancel h

def twoSiteTailBC0 : Matrix (Fin 6) (Fin 6) ℂ :=
  (twoSiteTailB0).realMatrix.map (algebraMap ℝ ℂ)

def twoSiteTailBC2 : Matrix (Fin 6) (Fin 6) ℂ :=
  (twoSiteTailB2).realMatrix.map (algebraMap ℝ ℂ)

private theorem twoSiteTailBC0_row (i : Fin 5) :
    ((twoSiteTailBC0 - Matrix.scalar (Fin 6) (-2) : Matrix (Fin 6) (Fin 6) ℂ) i.succ i.succ).re +
      ∑ j ∈ (Finset.univ : Finset (Fin 5)).erase i,
        ‖(twoSiteTailBC0 - Matrix.scalar (Fin 6) (-2) : Matrix (Fin 6) (Fin 6) ℂ) i.succ j.succ‖ ≤
          -(1 / 4 : ℝ) := by
  fin_cases i <;> norm_num [twoSiteTailBC0, twoSiteTailB0,
    ScaledIntegerMatrix.realMatrix, Matrix.sub_apply, Matrix.scalar_apply,
    Finset.sum_erase, Fin.sum_univ_succ]

private theorem twoSiteTailBC0_col (i : Fin 5) :
    ‖(twoSiteTailBC0 - Matrix.scalar (Fin 6) (-2) : Matrix (Fin 6) (Fin 6) ℂ) i.succ 0‖ ≤
      (1 / 500 : ℝ) := by
  fin_cases i <;> norm_num [twoSiteTailBC0, twoSiteTailB0,
    ScaledIntegerMatrix.realMatrix, Matrix.sub_apply, Matrix.scalar_apply]

private theorem twoSiteTailBC0_feedback :
    (∑ i : Fin 5,
      ‖(twoSiteTailBC0 - Matrix.scalar (Fin 6) (-2) : Matrix (Fin 6) (Fin 6) ℂ) 0 i.succ‖) ≤
        (1 / 300 : ℝ) := by
  norm_num [twoSiteTailBC0, twoSiteTailB0,
    ScaledIntegerMatrix.realMatrix, Matrix.sub_apply, Matrix.scalar_apply,
    Fin.sum_univ_succ]

private theorem twoSiteTailBC2_row (i : Fin 5) :
    ((twoSiteTailBC2 - Matrix.scalar (Fin 6) (-2) : Matrix (Fin 6) (Fin 6) ℂ) i.succ i.succ).re +
      ∑ j ∈ (Finset.univ : Finset (Fin 5)).erase i,
        ‖(twoSiteTailBC2 - Matrix.scalar (Fin 6) (-2) : Matrix (Fin 6) (Fin 6) ℂ) i.succ j.succ‖ ≤
          -(1 / 4 : ℝ) := by
  fin_cases i <;> norm_num [twoSiteTailBC2, twoSiteTailB2,
    ScaledIntegerMatrix.realMatrix, Matrix.sub_apply, Matrix.scalar_apply,
    Finset.sum_erase, Fin.sum_univ_succ]

private theorem twoSiteTailBC2_col (i : Fin 5) :
    ‖(twoSiteTailBC2 - Matrix.scalar (Fin 6) (-2) : Matrix (Fin 6) (Fin 6) ℂ) i.succ 0‖ ≤
      (1 / 500 : ℝ) := by
  fin_cases i <;> norm_num [twoSiteTailBC2, twoSiteTailB2,
    ScaledIntegerMatrix.realMatrix, Matrix.sub_apply, Matrix.scalar_apply]

private theorem twoSiteTailBC2_feedback :
    (∑ i : Fin 5,
      ‖(twoSiteTailBC2 - Matrix.scalar (Fin 6) (-2) : Matrix (Fin 6) (Fin 6) ℂ) 0 i.succ‖) ≤
        (1 / 300 : ℝ) := by
  norm_num [twoSiteTailBC2, twoSiteTailB2,
    ScaledIntegerMatrix.realMatrix, Matrix.sub_apply, Matrix.scalar_apply,
    Fin.sum_univ_succ]

theorem twoSiteTailBC0_unique_above_neg_two (z z' : ℂ)
    (hz : -2 ≤ z.re) (hz' : -2 ≤ z'.re)
    (hroot : twoSiteTailBC0.charpoly.eval z = 0)
    (hroot' : twoSiteTailBC0.charpoly.eval z' = 0) : z = z' :=
  unique_above_neg_two_of_shifted_bounds twoSiteTailBC0
    twoSiteTailBC0_row twoSiteTailBC0_col twoSiteTailBC0_feedback
    z z' hz hz' hroot hroot'

theorem twoSiteTailBC2_unique_above_neg_two (z z' : ℂ)
    (hz : -2 ≤ z.re) (hz' : -2 ≤ z'.re)
    (hroot : twoSiteTailBC2.charpoly.eval z = 0)
    (hroot' : twoSiteTailBC2.charpoly.eval z' = 0) : z = z' :=
  unique_above_neg_two_of_shifted_bounds twoSiteTailBC2
    twoSiteTailBC2_row twoSiteTailBC2_col twoSiteTailBC2_feedback
    z z' hz hz' hroot hroot'

private theorem simple_above_neg_two_of_shifted_bounds
    (M : Matrix (Fin 6) (Fin 6) ℂ)
    (hrow : ∀ i : Fin 5,
      ((M - Matrix.scalar (Fin 6) (-2) : Matrix (Fin 6) (Fin 6) ℂ) i.succ i.succ).re +
        ∑ j ∈ (Finset.univ : Finset (Fin 5)).erase i,
          ‖(M - Matrix.scalar (Fin 6) (-2) : Matrix (Fin 6) (Fin 6) ℂ) i.succ j.succ‖ ≤
            -(1 / 4 : ℝ))
    (hcol : ∀ i : Fin 5,
      ‖(M - Matrix.scalar (Fin 6) (-2) : Matrix (Fin 6) (Fin 6) ℂ) i.succ 0‖ ≤ (1 / 500 : ℝ))
    (hfeedback :
      (∑ i : Fin 5,
        ‖(M - Matrix.scalar (Fin 6) (-2) : Matrix (Fin 6) (Fin 6) ℂ) 0 i.succ‖) ≤
          (1 / 300 : ℝ))
    (z : ℂ) (hz : -2 ≤ z.re) (hroot : M.charpoly.eval z = 0) :
    M.charpoly.derivative.eval z ≠ 0 := by
  have hshift := block_spectrum_simple_right
    (M - Matrix.scalar (Fin 6) (-2) : Matrix (Fin 6) (Fin 6) ℂ)
    (1 / 4) (1 / 500) (1 / 100) (1 / 300)
    (by norm_num) hrow hcol (by norm_num) (by norm_num)
    hfeedback (by norm_num) (z + 2)
    (by simp; linarith) (shifted_root_of_root M z hroot)
  rw [Matrix.charpoly_sub_scalar, Polynomial.derivative_comp] at hshift
  simpa [Polynomial.eval_comp] using hshift

theorem twoSiteTailBC0_simple_above_neg_two (z : ℂ)
    (hz : -2 ≤ z.re) (hroot : twoSiteTailBC0.charpoly.eval z = 0) :
    twoSiteTailBC0.charpoly.derivative.eval z ≠ 0 :=
  simple_above_neg_two_of_shifted_bounds twoSiteTailBC0
    twoSiteTailBC0_row twoSiteTailBC0_col twoSiteTailBC0_feedback z hz hroot

theorem twoSiteTailBC2_simple_above_neg_two (z : ℂ)
    (hz : -2 ≤ z.re) (hroot : twoSiteTailBC2.charpoly.eval z = 0) :
    twoSiteTailBC2.charpoly.derivative.eval z ≠ 0 :=
  simple_above_neg_two_of_shifted_bounds twoSiteTailBC2
    twoSiteTailBC2_row twoSiteTailBC2_col twoSiteTailBC2_feedback z hz hroot

end
end PhosphorylationStableCapacity
