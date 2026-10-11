module
public import proofs.PhosphorylationStableCapacity.FiniteThreeSiteOperationalScales
public import proofs.PhosphorylationStableCapacity.FiniteThreeSiteOperationalZero
public import proofs.PhosphorylationStableCapacity.FiniteThreeSiteOperationalTwo
public import proofs.PhosphorylationStableCapacity.FiniteThreeSiteOperationalFour
public import proofs.PhosphorylationStableCapacity.BenchmarkOperationalPositivityZero
public import proofs.PhosphorylationStableCapacity.BenchmarkOperationalPositivityTwo
public import proofs.PhosphorylationStableCapacity.BenchmarkOperationalPositivityFour

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section
open PhosphorylationSharpness

theorem benchmarkThreeSiteMatrixFin_zero_hurwitz :
    IsHurwitz (benchmarkThreeSiteMatrixFin 0) := by
  intro z hz
  have hpoly :
      ((operationalZeroJ.realMatrix.map (algebraMap ℝ ℂ)).charpoly) =
        (((benchmarkThreeSiteMatrixFin 0).map (algebraMap ℝ ℂ)).charpoly) := by
    rw [← benchmarkThreeSiteWeightedJacobian_zero,
      Matrix.charpoly_map, Matrix.charpoly_map,
      benchmarkThreeSiteWeighted_charpoly]
  exact operationalZeroJ_hurwitz z (by rwa [hpoly])

theorem benchmarkThreeSiteMatrixFin_two_hurwitz :
    IsHurwitz (benchmarkThreeSiteMatrixFin 2) := by
  intro z hz
  have hpoly :
      ((operationalTwoJ.realMatrix.map (algebraMap ℝ ℂ)).charpoly) =
        (((benchmarkThreeSiteMatrixFin 2).map (algebraMap ℝ ℂ)).charpoly) := by
    rw [← benchmarkThreeSiteWeightedJacobian_two,
      Matrix.charpoly_map, Matrix.charpoly_map,
      benchmarkThreeSiteWeighted_charpoly]
  exact operationalTwoJ_hurwitz z (by rwa [hpoly])

theorem benchmarkThreeSiteMatrixFin_four_hurwitz :
    IsHurwitz (benchmarkThreeSiteMatrixFin 4) := by
  intro z hz
  have hpoly :
      ((operationalFourJ.realMatrix.map (algebraMap ℝ ℂ)).charpoly) =
        (((benchmarkThreeSiteMatrixFin 4).map (algebraMap ℝ ℂ)).charpoly) := by
    rw [← benchmarkThreeSiteWeightedJacobian_four,
      Matrix.charpoly_map, Matrix.charpoly_map,
      benchmarkThreeSiteWeighted_charpoly]
  exact operationalFourJ_hurwitz z (by rwa [hpoly])

theorem benchmarkThreeSite_linearly_stable_of_fin (j : Fin 5)
    (h : IsHurwitz (benchmarkThreeSiteMatrixFin j)) :
    IsLinearlyStable 18 2 20 benchmarkThreeSiteRates
      (benchmarkThreeSiteCoord j) := by
  intro z hz
  have hchar :
      (restrictedJacobianMatrix 18 2 20 benchmarkThreeSiteRates
        (benchmarkThreeSiteCoord j)).charpoly =
        (benchmarkThreeSiteMatrixFin j).charpoly := by
    exact (Matrix.charpoly_reindex _ _).symm
  apply h z
  simpa only [Matrix.charpoly_map, hchar] using hz

theorem benchmarkThreeSite_zero_linearly_stable :
    IsLinearlyStable 18 2 20 benchmarkThreeSiteRates
      (benchmarkThreeSiteCoord 0) :=
  benchmarkThreeSite_linearly_stable_of_fin 0 benchmarkThreeSiteMatrixFin_zero_hurwitz

theorem benchmarkThreeSite_two_linearly_stable :
    IsLinearlyStable 18 2 20 benchmarkThreeSiteRates
      (benchmarkThreeSiteCoord 2) :=
  benchmarkThreeSite_linearly_stable_of_fin 2 benchmarkThreeSiteMatrixFin_two_hurwitz

theorem benchmarkThreeSite_four_linearly_stable :
    IsLinearlyStable 18 2 20 benchmarkThreeSiteRates
      (benchmarkThreeSiteCoord 4) :=
  benchmarkThreeSite_linearly_stable_of_fin 4 benchmarkThreeSiteMatrixFin_four_hurwitz

end
end PhosphorylationStableCapacity
