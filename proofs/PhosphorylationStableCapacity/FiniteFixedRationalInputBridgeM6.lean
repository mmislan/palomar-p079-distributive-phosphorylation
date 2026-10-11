module
public import proofs.PhosphorylationStableCapacity.FiniteFixedRationalInputDataM6
public import proofs.PhosphorylationStableCapacity.FiniteFixedRationalLookupValidM6
public import Mathlib.Tactic.FinCases

@[expose] public section

namespace PhosphorylationStableCapacity
noncomputable section
open PhosphorylationSharpness
set_option maxHeartbeats 2000000
set_option maxRecDepth 8192

theorem finiteFixedRatesQM6_eq_lookup : finiteFixedRatesQM6 = finiteFixedLookupM6.rates := by
  unfold finiteFixedRatesQM6 FixedRationalLookup.rates
  congr 1 <;> funext i <;> fin_cases i <;> decide +kernel

theorem finiteFixedRatesQM6_toReal : finiteFixedRatesQM6.toReal = finiteFixedPrintedRates 6 := by
  rw [finiteFixedRatesQM6_eq_lookup]
  exact finiteFixedLookupM6_valid.rates_cast

theorem finiteFixedCoordinatesQM6_eq_lookup (j : Fin 13) :
    finiteFixedCoordinatesQM6 j = finiteFixedLookupM6.coordinate j := by
  apply Prod.ext
  · funext i
    fin_cases j <;> fin_cases i <;> decide +kernel
  · apply Prod.ext
    · funext i
      fin_cases j <;> fin_cases i <;> decide +kernel
    · funext i
      fin_cases j <;> fin_cases i <;> decide +kernel

theorem finiteFixedCoordinatesQM6_toReal (j : Fin 13) :
    (finiteFixedCoordinatesQM6 j).toReal =
      toCoordinateSpace (chart (finiteFixedPrintedState 6 j)) := by
  rw [finiteFixedCoordinatesQM6_eq_lookup]
  exact finiteFixedLookupM6_valid.coordinate_cast j

end
end PhosphorylationStableCapacity
