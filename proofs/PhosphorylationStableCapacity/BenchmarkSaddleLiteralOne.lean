module
public import proofs.PhosphorylationStableCapacity.FiniteThreeSiteOperationalJacobian
public import proofs.PhosphorylationStableCapacity.BenchmarkSaddleSimilarityOne
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.NormNum

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section
open PhosphorylationSharpness

set_option maxHeartbeats 2000000

theorem benchmarkSaddleOneA_eq_literal :
    benchmarkSaddleOneA.realMatrix = benchmarkThreeSiteMatrixFin 1 := by
  rw [benchmarkThreeSiteMatrixFin_eq_explicit]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [benchmarkSaddleOneA, ScaledIntegerMatrix.realMatrix,
      Matrix.map, Matrix.smul_apply, Matrix.of_apply,
      threeSiteExplicitJacobian, threeSiteFreeS0,
      threeSiteFreeE, threeSiteFreeF,
      benchmarkThreeSiteRates, benchmarkThreeSiteCoord,
      benchmarkThreeSiteStates, toCoordinateSpace, chart]

end
end PhosphorylationStableCapacity
