module
public import proofs.PhosphorylationStableCapacity.FiniteFixedRationalInputDataM3
public import proofs.PhosphorylationStableCapacity.FiniteFixedRationalLookupValidM3
public import Mathlib.Tactic.FinCases

@[expose] public section

namespace PhosphorylationStableCapacity
noncomputable section
open PhosphorylationSharpness
set_option maxHeartbeats 2000000
set_option maxRecDepth 8192

theorem finiteFixedRatesQM3_eq_lookup : finiteFixedRatesQM3 = finiteFixedLookupM3.rates := by
  unfold finiteFixedRatesQM3 FixedRationalLookup.rates
  congr 1 <;> funext i <;> fin_cases i <;> decide +kernel

theorem finiteFixedRatesQM3_toReal : finiteFixedRatesQM3.toReal = finiteFixedPrintedRates 3 := by
  rw [finiteFixedRatesQM3_eq_lookup]
  exact finiteFixedLookupM3_valid.rates_cast

theorem finiteFixedCoordinatesQM3_eq_lookup (j : Fin 7) :
    finiteFixedCoordinatesQM3 j = finiteFixedLookupM3.coordinate j := by
  apply Prod.ext
  · funext i
    fin_cases j <;> fin_cases i <;> decide +kernel
  · apply Prod.ext
    · funext i
      fin_cases j <;> fin_cases i <;> decide +kernel
    · funext i
      fin_cases j <;> fin_cases i <;> decide +kernel

theorem finiteFixedCoordinatesQM3_toReal (j : Fin 7) :
    (finiteFixedCoordinatesQM3 j).toReal =
      toCoordinateSpace (chart (finiteFixedPrintedState 3 j)) := by
  rw [finiteFixedCoordinatesQM3_eq_lookup]
  exact finiteFixedLookupM3_valid.coordinate_cast j

end
end PhosphorylationStableCapacity
