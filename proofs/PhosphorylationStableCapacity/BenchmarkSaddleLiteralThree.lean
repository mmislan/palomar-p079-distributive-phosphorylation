module
public import proofs.PhosphorylationStableCapacity.FiniteThreeSiteOperationalJacobian
public import proofs.PhosphorylationStableCapacity.BenchmarkSaddleSimilarityThree
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.NormNum

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section
open PhosphorylationSharpness

set_option maxHeartbeats 2000000

theorem benchmarkSaddleThreeA_eq_literal :
    benchmarkSaddleThreeA.realMatrix = benchmarkThreeSiteMatrixFin 3 := by
  rw [benchmarkThreeSiteMatrixFin_eq_explicit]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [benchmarkSaddleThreeA, ScaledIntegerMatrix.realMatrix,
      Matrix.map, Matrix.smul_apply, Matrix.of_apply,
      threeSiteExplicitJacobian, threeSiteFreeS0,
      threeSiteFreeE, threeSiteFreeF,
      benchmarkThreeSiteRates, benchmarkThreeSiteCoord,
      benchmarkThreeSiteStates, toCoordinateSpace, chart]

end
end PhosphorylationStableCapacity
