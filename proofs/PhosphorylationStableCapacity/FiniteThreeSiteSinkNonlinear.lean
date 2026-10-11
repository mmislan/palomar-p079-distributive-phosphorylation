module
public import proofs.PhosphorylationStableCapacity.FiniteThreeSiteSinkSpectra
public import proofs.PhosphorylationStableCapacity.FiniteThreeSiteBenchmarkEquilibria
public import proofs.PhosphorylationStableCapacity.HurwitzNonlinearStability

@[expose] public section
set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

namespace PhosphorylationStableCapacity

noncomputable section
open PhosphorylationSharpness

private theorem benchmarkThreeSite_restricted_zero (j : Fin 5) :
    restrictedFieldEuclid 18 2 20 benchmarkThreeSiteRates
      (benchmarkThreeSiteCoord j) = 0 := by
  apply (restrictedFieldEuclid_eq_zero_iff 18 2 20 benchmarkThreeSiteRates
    (benchmarkThreeSiteCoord j)).2
  simpa only [benchmarkThreeSiteCoord, of_toCoordinateSpace,
    unChart_chart_of_inClass 18 2 20 (benchmarkThreeSiteStates j)
      (benchmarkThreeSiteStates_inClass j)] using
    benchmarkThreeSiteStates_equilibrium j

private theorem benchmarkThreeSite_coord_strict (j : Fin 5) :
    benchmarkThreeSiteCoord j ∈ classPolytopeStrict 3 18 2 20 := by
  exact positive_state_mem_classPolytopeStrict 18 2 20
    (benchmarkThreeSiteStates j)
    (benchmarkThreeSiteStates_positive j)
    (benchmarkThreeSiteStates_inClass j)

theorem benchmarkThreeSite_zero_nonlinear_sink :
    IsLocallyAsymptoticallyStableClass 18 2 20 benchmarkThreeSiteRates
      (benchmarkThreeSiteCoord 0) := by
  exact isLinearlyStable_locally_asymptotically_stable
    (by norm_num : 1 ≤ 3) 18 2 20 (by norm_num)
    benchmarkThreeSiteRates benchmarkThreeSiteRates_positive
    (benchmarkThreeSiteCoord 0) (benchmarkThreeSite_coord_strict 0)
    (benchmarkThreeSite_restricted_zero 0)
    benchmarkThreeSite_zero_linearly_stable

theorem benchmarkThreeSite_two_nonlinear_sink :
    IsLocallyAsymptoticallyStableClass 18 2 20 benchmarkThreeSiteRates
      (benchmarkThreeSiteCoord 2) := by
  exact isLinearlyStable_locally_asymptotically_stable
    (by norm_num : 1 ≤ 3) 18 2 20 (by norm_num)
    benchmarkThreeSiteRates benchmarkThreeSiteRates_positive
    (benchmarkThreeSiteCoord 2) (benchmarkThreeSite_coord_strict 2)
    (benchmarkThreeSite_restricted_zero 2)
    benchmarkThreeSite_two_linearly_stable

theorem benchmarkThreeSite_four_nonlinear_sink :
    IsLocallyAsymptoticallyStableClass 18 2 20 benchmarkThreeSiteRates
      (benchmarkThreeSiteCoord 4) := by
  exact isLinearlyStable_locally_asymptotically_stable
    (by norm_num : 1 ≤ 3) 18 2 20 (by norm_num)
    benchmarkThreeSiteRates benchmarkThreeSiteRates_positive
    (benchmarkThreeSiteCoord 4) (benchmarkThreeSite_coord_strict 4)
    (benchmarkThreeSite_restricted_zero 4)
    benchmarkThreeSite_four_linearly_stable

end
end PhosphorylationStableCapacity
