module
public import proofs.PhosphorylationStableCapacity.BenchmarkSaddleDetPilotOne
public import proofs.PhosphorylationStableCapacity.ScaledIntegerDeterminantSign
public import proofs.PhosphorylationStableCapacity.PositiveCharpolyRootFromNegativeConstant
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
public import Mathlib.Tactic.Linarith

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section

theorem benchmarkSaddleOneA_real_det_positive :
    0 < benchmarkSaddleOneA.realMatrix.det :=
  ScaledIntegerMatrix.realMatrix_det_pos benchmarkSaddleOneA
    (by decide) benchmarkSaddleOneA_integer_det_positive

theorem benchmarkSaddleOneA_charpoly_constant_negative :
    benchmarkSaddleOneA.realMatrix.charpoly.coeff 0 < 0 := by
  have hdet := Matrix.det_eq_sign_charpoly_coeff benchmarkSaddleOneA.realMatrix
  norm_num at hdet
  linarith [benchmarkSaddleOneA_real_det_positive]

theorem benchmarkSaddleOneA_exists_positive_root :
    ∃ x : ℝ, 0 < x ∧ benchmarkSaddleOneA.realMatrix.charpoly.eval x = 0 :=
  positive_charpoly_root_of_negative_constant benchmarkSaddleOneA.realMatrix
    benchmarkSaddleOneA_charpoly_constant_negative

end
end PhosphorylationStableCapacity
