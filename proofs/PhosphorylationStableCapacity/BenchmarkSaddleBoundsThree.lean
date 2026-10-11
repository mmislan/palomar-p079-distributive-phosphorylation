module
public import proofs.PhosphorylationStableCapacity.BenchmarkSaddleSimilarityThree
public import proofs.PhosphorylationStableCapacity.SaddleSmallGainMatrix
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.NormNum

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section
open scoped Matrix

set_option maxHeartbeats 2000000

def benchmarkSaddleThreeBC : Matrix (Fin 9) (Fin 9) ℂ :=
  benchmarkSaddleThreeB.realMatrix.map (algebraMap ℝ ℂ)

theorem benchmarkSaddleThreeBC_charpoly_eq_AC :
    benchmarkSaddleThreeBC.charpoly =
      (benchmarkSaddleThreeA.realMatrix.map (algebraMap ℝ ℂ)).charpoly := by
  rw [benchmarkSaddleThreeBC, Matrix.charpoly_map, benchmarkSaddleThree_B_charpoly_eq_A,
    ← Matrix.charpoly_map]

theorem benchmarkSaddleThree_row_bound (i : Fin 8) :
    (benchmarkSaddleThreeBC i.succ i.succ).re +
      ∑ j ∈ (Finset.univ : Finset (Fin 8)).erase i,
        ‖benchmarkSaddleThreeBC i.succ j.succ‖ ≤ -(1 / 20 : ℝ) := by
  fin_cases i <;> norm_num [benchmarkSaddleThreeBC, benchmarkSaddleThreeB,
    ScaledIntegerMatrix.realMatrix, Matrix.map,
    Matrix.smul_apply, Matrix.of_apply,
    Finset.sum_erase, Fin.sum_univ_succ]

theorem benchmarkSaddleThree_col_bound (i : Fin 8) :
    ‖benchmarkSaddleThreeBC i.succ 0‖ ≤ (1 / 500 : ℝ) := by
  fin_cases i <;> norm_num [benchmarkSaddleThreeBC, benchmarkSaddleThreeB,
    ScaledIntegerMatrix.realMatrix, Matrix.map,
    Matrix.smul_apply, Matrix.of_apply]

theorem benchmarkSaddleThree_feedback_bound :
    (∑ i : Fin 8, ‖benchmarkSaddleThreeBC 0 i.succ‖) ≤ (1 / 400 : ℝ) := by
  norm_num [benchmarkSaddleThreeBC, benchmarkSaddleThreeB,
    ScaledIntegerMatrix.realMatrix, Matrix.map,
    Matrix.smul_apply, Matrix.of_apply, Fin.sum_univ_succ]

theorem benchmarkSaddleThree_unique_right (z z' : ℂ)
    (hz : 0 ≤ z.re) (hz' : 0 ≤ z'.re)
    (hr : benchmarkSaddleThreeBC.charpoly.eval z = 0)
    (hr' : benchmarkSaddleThreeBC.charpoly.eval z' = 0) : z = z' := by
  apply block_spectrum_unique_right benchmarkSaddleThreeBC (1 / 20) (1 / 500) (1 / 20) (1 / 400)
    (by norm_num) benchmarkSaddleThree_row_bound benchmarkSaddleThree_col_bound
    (by norm_num) (by norm_num) benchmarkSaddleThree_feedback_bound (by norm_num)
    z z' hz hz' hr hr'

end
end PhosphorylationStableCapacity
