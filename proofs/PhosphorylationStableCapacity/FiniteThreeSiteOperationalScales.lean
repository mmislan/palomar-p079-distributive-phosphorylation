module
public import proofs.PhosphorylationStableCapacity.FiniteThreeSiteOperationalJacobian
public import proofs.PhosphorylationStableCapacity.DiagonalWeightedCharpoly
public import Mathlib.Tactic.FinCases

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section

set_option maxHeartbeats 2000000

theorem benchmarkThreeSiteFlat_positive (j : Fin 5) (i : Fin 9) :
    0 < benchmarkThreeSiteFlat j i := by
  fin_cases j <;> fin_cases i <;>
    norm_num [benchmarkThreeSiteFlat, benchmarkThreeSiteCoord,
      benchmarkThreeSiteStates, toCoordinateSpace,
      PhosphorylationStableCapacity.chart]

theorem benchmarkThreeSiteWeighted_charpoly (j : Fin 5) :
    (benchmarkThreeSiteWeightedJacobian j).charpoly =
      (benchmarkThreeSiteMatrixFin j).charpoly := by
  exact diagonal_weighted_charpoly (benchmarkThreeSiteMatrixFin j)
    (benchmarkThreeSiteFlat j)
    (fun i => ne_of_gt (benchmarkThreeSiteFlat_positive j i))

end
end PhosphorylationStableCapacity
