module
public import proofs.PhosphorylationStableCapacity.FiniteFixedRationalInputDataM5
public import proofs.PhosphorylationStableCapacity.FiniteFixedRationalLookupValidM5
public import Mathlib.Tactic.FinCases

@[expose] public section

namespace PhosphorylationStableCapacity
noncomputable section
open PhosphorylationSharpness
set_option maxHeartbeats 2000000
set_option maxRecDepth 8192

theorem finiteFixedRatesQM5_eq_lookup : finiteFixedRatesQM5 = finiteFixedLookupM5.rates := by
  unfold finiteFixedRatesQM5 FixedRationalLookup.rates
  congr 1 <;> funext i <;> fin_cases i <;> decide +kernel

theorem finiteFixedRatesQM5_toReal : finiteFixedRatesQM5.toReal = finiteFixedPrintedRates 5 := by
  rw [finiteFixedRatesQM5_eq_lookup]
  exact finiteFixedLookupM5_valid.rates_cast

theorem finiteFixedCoordinatesQM5_eq_lookup (j : Fin 11) :
    finiteFixedCoordinatesQM5 j = finiteFixedLookupM5.coordinate j := by
  apply Prod.ext
  · funext i
    fin_cases j <;> fin_cases i <;> decide +kernel
  · apply Prod.ext
    · funext i
      fin_cases j <;> fin_cases i <;> decide +kernel
    · funext i
      fin_cases j <;> fin_cases i <;> decide +kernel

theorem finiteFixedCoordinatesQM5_toReal (j : Fin 11) :
    (finiteFixedCoordinatesQM5 j).toReal =
      toCoordinateSpace (chart (finiteFixedPrintedState 5 j)) := by
  rw [finiteFixedCoordinatesQM5_eq_lookup]
  exact finiteFixedLookupM5_valid.coordinate_cast j

end
end PhosphorylationStableCapacity
