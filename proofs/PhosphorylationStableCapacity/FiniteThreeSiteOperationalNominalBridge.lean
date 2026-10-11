module
public import proofs.PhosphorylationStableCapacity.FiniteThreeSiteBenchmarkData
public import proofs.PhosphorylationStableCapacity.BenchmarkOperationalIntervalZero
public import proofs.PhosphorylationStableCapacity.BenchmarkOperationalIntervalTwo
public import proofs.PhosphorylationStableCapacity.BenchmarkOperationalIntervalFour
public import proofs.PhosphorylationStableCapacity.OperationalWeightedCoordinates
public import Mathlib.Tactic.FinCases

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section
open PhosphorylationSharpness

set_option maxHeartbeats 2000000

/-- The zero-profile operational box is centred at the printed first equilibrium. -/
theorem benchmarkThreeSiteFlat_zero_eq_operational_centre :
    benchmarkThreeSiteFlat 0 =
      fun i => (operationalZeroIntervalCoordinates i : ℝ) := by
  funext i
  fin_cases i <;>
    norm_num [benchmarkThreeSiteFlat, benchmarkThreeSiteCoord,
      benchmarkThreeSiteStates, operationalZeroIntervalCoordinates,
      toCoordinateSpace, chart]

/-- The two-profile operational box is centred at the printed third equilibrium. -/
theorem benchmarkThreeSiteFlat_two_eq_operational_centre :
    benchmarkThreeSiteFlat 2 =
      fun i => (operationalTwoIntervalCoordinates i : ℝ) := by
  funext i
  fin_cases i <;>
    norm_num [benchmarkThreeSiteFlat, benchmarkThreeSiteCoord,
      benchmarkThreeSiteStates, operationalTwoIntervalCoordinates,
      toCoordinateSpace, chart]

/-- The four-profile operational box is centred at the printed fifth equilibrium. -/
theorem benchmarkThreeSiteFlat_four_eq_operational_centre :
    benchmarkThreeSiteFlat 4 =
      fun i => (operationalFourIntervalCoordinates i : ℝ) := by
  funext i
  fin_cases i <;>
    norm_num [benchmarkThreeSiteFlat, benchmarkThreeSiteCoord,
      benchmarkThreeSiteStates, operationalFourIntervalCoordinates,
      toCoordinateSpace, chart]

/-- The interval's 21 nominal parameters are the printed benchmark rates and totals. -/
def benchmarkThreeSiteOperationalNominal : Fin 21 → ℝ :=
  fun i => (operationalZeroIntervalNominal (Fin.castAdd 9 i) : ℝ)

theorem benchmarkThreeSiteOperationalNominal_zero :
    benchmarkThreeSiteOperationalNominal =
      (fun i : Fin 21 =>
        (operationalZeroIntervalNominal (Fin.castAdd 9 i) : ℝ)) := rfl

theorem benchmarkThreeSiteOperationalNominal_two :
    benchmarkThreeSiteOperationalNominal =
      (fun i : Fin 21 =>
        (operationalTwoIntervalNominal (Fin.castAdd 9 i) : ℝ)) := by
  funext i
  fin_cases i <;>
    norm_num [benchmarkThreeSiteOperationalNominal,
      operationalZeroIntervalNominal, operationalTwoIntervalNominal]

theorem benchmarkThreeSiteOperationalNominal_four :
    benchmarkThreeSiteOperationalNominal =
      (fun i : Fin 21 =>
        (operationalFourIntervalNominal (Fin.castAdd 9 i) : ℝ)) := by
  funext i
  fin_cases i <;>
    norm_num [benchmarkThreeSiteOperationalNominal,
      operationalZeroIntervalNominal, operationalFourIntervalNominal]

theorem benchmarkThreeSiteRates_eq_operational_nominal :
    operationalParameterRates
      benchmarkThreeSiteOperationalNominal =
        benchmarkThreeSiteRates := by
  unfold operationalParameterRates benchmarkThreeSiteRates
  congr 1 <;> funext i <;> fin_cases i <;>
    norm_num [benchmarkThreeSiteOperationalNominal, operationalZeroIntervalNominal]

theorem benchmarkThreeSiteTotals_eq_operational_nominal :
    (benchmarkThreeSiteOperationalNominal 18,
      benchmarkThreeSiteOperationalNominal 19,
      benchmarkThreeSiteOperationalNominal 20) = (18, 2, 20) := by
  norm_num [benchmarkThreeSiteOperationalNominal,
    operationalZeroIntervalNominal]

end
end PhosphorylationStableCapacity
