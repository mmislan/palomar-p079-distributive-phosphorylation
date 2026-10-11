module
public import proofs.PhosphorylationStableCapacity.FiniteThreeSiteJacobianMatrix
public import proofs.PhosphorylationStableCapacity.FiniteThreeSiteBenchmarkData

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section
open PhosphorylationSharpness

set_option maxHeartbeats 2000000

/-- The literal class Jacobian for each benchmark profile, in the printed
nine-coordinate order. -/
def benchmarkThreeSiteMatrixFin (j : Fin 5) : Matrix (Fin 9) (Fin 9) ℝ :=
  Matrix.reindex threeSiteIndexEquiv threeSiteIndexEquiv
    (restrictedJacobianMatrix 18 2 20 benchmarkThreeSiteRates
      (benchmarkThreeSiteCoord j))

theorem benchmarkThreeSiteMatrixFin_eq_explicit (j : Fin 5) :
    benchmarkThreeSiteMatrixFin j =
      threeSiteExplicitJacobian 18 2 20 benchmarkThreeSiteRates
        (benchmarkThreeSiteCoord j) :=
  threeSiteMatrixFin_eq_explicit 18 2 20 benchmarkThreeSiteRates
    (benchmarkThreeSiteCoord j)

/-- Coordinate scaling used by the operational spectral certificates. -/
def benchmarkThreeSiteWeightedJacobian (j : Fin 5) :
    Matrix (Fin 9) (Fin 9) ℝ :=
  Matrix.of fun i l =>
    benchmarkThreeSiteMatrixFin j i l *
    benchmarkThreeSiteFlat j l / benchmarkThreeSiteFlat j i


end
end PhosphorylationStableCapacity
