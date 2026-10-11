module
public import proofs.PhosphorylationStableCapacity.FiniteThreeSiteOperationalJacobian
public import proofs.PhosphorylationStableCapacity.BenchmarkOperationalInverseZero

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section
open PhosphorylationSharpness

set_option maxHeartbeats 2000000

theorem benchmarkThreeSiteWeightedJacobian_zero :
    benchmarkThreeSiteWeightedJacobian 0 = operationalZeroJ.realMatrix := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [benchmarkThreeSiteWeightedJacobian,
      benchmarkThreeSiteMatrixFin_eq_explicit, threeSiteExplicitJacobian,
      threeSiteFreeS0, threeSiteFreeE, threeSiteFreeF,
      benchmarkThreeSiteFlat, benchmarkThreeSiteCoord,
      benchmarkThreeSiteStates, benchmarkThreeSiteRates,
      operationalZeroJ, ScaledIntegerMatrix.realMatrix,
      Matrix.map, Matrix.smul_apply, Matrix.of_apply,
      toCoordinateSpace, chart]


end
end PhosphorylationStableCapacity
