module
public import proofs.PhosphorylationStableCapacity.SaddleSimilarityData
public import proofs.PhosphorylationStableCapacity.SaddleSmallGainMatrix
public import Mathlib.Tactic.NormNum

@[expose] public section
set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

namespace PhosphorylationStableCapacity

noncomputable section

def saddleBC : Matrix (Fin 6) (Fin 6) ℂ :=
  saddleB.realMatrix.map (algebraMap ℝ ℂ)

theorem saddleBC_charpoly_eq_saddleAC :
    saddleBC.charpoly =
      (saddleA.realMatrix.map (algebraMap ℝ ℂ)).charpoly := by
  rw [saddleBC, Matrix.charpoly_map, saddleB_charpoly_eq_saddleA,
    ← Matrix.charpoly_map]

private theorem saddleB_row_bound (i : Fin 5) :
    (saddleBC i.succ i.succ).re +
      ∑ j ∈ (Finset.univ : Finset (Fin 5)).erase i,
        ‖saddleBC i.succ j.succ‖ ≤ -(2 : ℝ) := by
  fin_cases i <;> norm_num [saddleBC, saddleB,
    ScaledIntegerMatrix.realMatrix, Finset.sum_erase,
    Fin.sum_univ_succ]

private theorem saddleB_col_bound (i : Fin 5) :
    ‖saddleBC i.succ 0‖ ≤ (1 / 100 : ℝ) := by
  fin_cases i <;> norm_num [saddleBC, saddleB,
    ScaledIntegerMatrix.realMatrix]

private theorem saddleB_feedback_bound :
    (∑ i : Fin 5, ‖saddleBC 0 i.succ‖) ≤ (1 / 50 : ℝ) := by
  norm_num [saddleBC, saddleB, ScaledIntegerMatrix.realMatrix,
    Fin.sum_univ_succ]

/-- The exact rational similar matrix has at most one eigenvalue with
nonnegative real part. -/
theorem saddleB_unique_right (z z' : ℂ)
    (hz : 0 ≤ z.re) (hz' : 0 ≤ z'.re)
    (hr : saddleBC.charpoly.eval z = 0)
    (hr' : saddleBC.charpoly.eval z' = 0) : z = z' := by
  apply block_spectrum_unique_right saddleBC 2 (1 / 100) (1 / 100) (1 / 50)
    (by norm_num) saddleB_row_bound saddleB_col_bound
    (by norm_num) (by norm_num) saddleB_feedback_bound (by norm_num)
    z z' hz hz' hr hr'

end
end PhosphorylationStableCapacity
