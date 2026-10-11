module
public import proofs.PhosphorylationStableCapacity.FiniteFixedRationalInputDataM4
public import proofs.PhosphorylationStableCapacity.FiniteFixedRationalLookupValidM4
public import Mathlib.Tactic.FinCases

@[expose] public section

namespace PhosphorylationStableCapacity
noncomputable section
open PhosphorylationSharpness
set_option maxHeartbeats 2000000
set_option maxRecDepth 8192

theorem finiteFixedRatesQM4_eq_lookup : finiteFixedRatesQM4 = finiteFixedLookupM4.rates := by
  unfold finiteFixedRatesQM4 FixedRationalLookup.rates
  congr 1 <;> funext i <;> fin_cases i <;> decide +kernel

theorem finiteFixedRatesQM4_toReal : finiteFixedRatesQM4.toReal = finiteFixedPrintedRates 4 := by
  rw [finiteFixedRatesQM4_eq_lookup]
  exact finiteFixedLookupM4_valid.rates_cast

theorem finiteFixedCoordinatesQM4_eq_lookup (j : Fin 9) :
    finiteFixedCoordinatesQM4 j = finiteFixedLookupM4.coordinate j := by
  apply Prod.ext
  · funext i
    fin_cases j <;> fin_cases i <;> decide +kernel
  · apply Prod.ext
    · funext i
      fin_cases j <;> fin_cases i <;> decide +kernel
    · funext i
      fin_cases j <;> fin_cases i <;> decide +kernel

theorem finiteFixedCoordinatesQM4_toReal (j : Fin 9) :
    (finiteFixedCoordinatesQM4 j).toReal =
      toCoordinateSpace (chart (finiteFixedPrintedState 4 j)) := by
  rw [finiteFixedCoordinatesQM4_eq_lookup]
  exact finiteFixedLookupM4_valid.coordinate_cast j

end
end PhosphorylationStableCapacity
