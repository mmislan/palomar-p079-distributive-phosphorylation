module
public import proofs.PhosphorylationStableCapacity.BenchmarkSaddleDetPilotThree
public import proofs.PhosphorylationStableCapacity.ScaledIntegerDeterminantSign
public import proofs.PhosphorylationStableCapacity.PositiveCharpolyRootFromNegativeConstant
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
public import Mathlib.Tactic.Linarith

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section

theorem benchmarkSaddleThreeA_real_det_positive :
    0 < benchmarkSaddleThreeA.realMatrix.det :=
  ScaledIntegerMatrix.realMatrix_det_pos benchmarkSaddleThreeA
    (by decide) benchmarkSaddleThreeA_integer_det_positive

theorem benchmarkSaddleThreeA_charpoly_constant_negative :
    benchmarkSaddleThreeA.realMatrix.charpoly.coeff 0 < 0 := by
  have hdet := Matrix.det_eq_sign_charpoly_coeff benchmarkSaddleThreeA.realMatrix
  norm_num at hdet
  linarith [benchmarkSaddleThreeA_real_det_positive]

theorem benchmarkSaddleThreeA_exists_positive_root :
    ∃ x : ℝ, 0 < x ∧ benchmarkSaddleThreeA.realMatrix.charpoly.eval x = 0 :=
  positive_charpoly_root_of_negative_constant benchmarkSaddleThreeA.realMatrix
    benchmarkSaddleThreeA_charpoly_constant_negative

end
end PhosphorylationStableCapacity
