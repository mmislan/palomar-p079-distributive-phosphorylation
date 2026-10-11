module
public import proofs.PhosphorylationStableCapacity.FiniteThreeSiteOperationalJacobian
public import proofs.PhosphorylationStableCapacity.BenchmarkOperationalInverseFour

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section
open PhosphorylationSharpness

set_option maxHeartbeats 2000000

theorem benchmarkThreeSiteWeightedJacobian_four :
    benchmarkThreeSiteWeightedJacobian 4 = operationalFourJ.realMatrix := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [benchmarkThreeSiteWeightedJacobian,
      benchmarkThreeSiteMatrixFin_eq_explicit, threeSiteExplicitJacobian,
      threeSiteFreeS0, threeSiteFreeE, threeSiteFreeF,
      benchmarkThreeSiteFlat, benchmarkThreeSiteCoord,
      benchmarkThreeSiteStates, benchmarkThreeSiteRates,
      operationalFourJ, ScaledIntegerMatrix.realMatrix,
      Matrix.map, Matrix.smul_apply, Matrix.of_apply,
      toCoordinateSpace, chart]

end
end PhosphorylationStableCapacity
