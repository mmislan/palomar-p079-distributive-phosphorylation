module
public import proofs.PhosphorylationStableCapacity.BenchmarkSaddleSimilarityOne
public import proofs.PhosphorylationStableCapacity.SaddleSmallGainMatrix
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.NormNum

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section
open scoped Matrix

set_option maxHeartbeats 2000000

def benchmarkSaddleOneBC : Matrix (Fin 9) (Fin 9) ℂ :=
  benchmarkSaddleOneB.realMatrix.map (algebraMap ℝ ℂ)

theorem benchmarkSaddleOneBC_charpoly_eq_AC :
    benchmarkSaddleOneBC.charpoly =
      (benchmarkSaddleOneA.realMatrix.map (algebraMap ℝ ℂ)).charpoly := by
  rw [benchmarkSaddleOneBC, Matrix.charpoly_map, benchmarkSaddleOne_B_charpoly_eq_A,
    ← Matrix.charpoly_map]

theorem benchmarkSaddleOne_row_bound (i : Fin 8) :
    (benchmarkSaddleOneBC i.succ i.succ).re +
      ∑ j ∈ (Finset.univ : Finset (Fin 8)).erase i,
        ‖benchmarkSaddleOneBC i.succ j.succ‖ ≤ -(1 / 5 : ℝ) := by
  fin_cases i <;> norm_num [benchmarkSaddleOneBC, benchmarkSaddleOneB,
    ScaledIntegerMatrix.realMatrix, Matrix.map,
    Matrix.smul_apply, Matrix.of_apply,
    Finset.sum_erase, Fin.sum_univ_succ]

theorem benchmarkSaddleOne_col_bound (i : Fin 8) :
    ‖benchmarkSaddleOneBC i.succ 0‖ ≤ (1 / 1000 : ℝ) := by
  fin_cases i <;> norm_num [benchmarkSaddleOneBC, benchmarkSaddleOneB,
    ScaledIntegerMatrix.realMatrix, Matrix.map,
    Matrix.smul_apply, Matrix.of_apply]

theorem benchmarkSaddleOne_feedback_bound :
    (∑ i : Fin 8, ‖benchmarkSaddleOneBC 0 i.succ‖) ≤ (1 / 500 : ℝ) := by
  norm_num [benchmarkSaddleOneBC, benchmarkSaddleOneB,
    ScaledIntegerMatrix.realMatrix, Matrix.map,
    Matrix.smul_apply, Matrix.of_apply, Fin.sum_univ_succ]

theorem benchmarkSaddleOne_unique_right (z z' : ℂ)
    (hz : 0 ≤ z.re) (hz' : 0 ≤ z'.re)
    (hr : benchmarkSaddleOneBC.charpoly.eval z = 0)
    (hr' : benchmarkSaddleOneBC.charpoly.eval z' = 0) : z = z' := by
  apply block_spectrum_unique_right benchmarkSaddleOneBC (1 / 5) (1 / 1000) (1 / 100) (1 / 500)
    (by norm_num) benchmarkSaddleOne_row_bound benchmarkSaddleOne_col_bound
    (by norm_num) (by norm_num) benchmarkSaddleOne_feedback_bound (by norm_num)
    z z' hz hz' hr hr'

end
end PhosphorylationStableCapacity
