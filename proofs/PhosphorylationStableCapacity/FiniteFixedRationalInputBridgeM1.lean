module
public import proofs.PhosphorylationStableCapacity.FiniteFixedRationalInputDataM1
public import proofs.PhosphorylationStableCapacity.FiniteFixedRationalLookupValidM1
public import Mathlib.Tactic.FinCases

@[expose] public section

namespace PhosphorylationStableCapacity
noncomputable section
open PhosphorylationSharpness
set_option maxHeartbeats 2000000
set_option maxRecDepth 8192

theorem finiteFixedRatesQM1_eq_lookup : finiteFixedRatesQM1 = finiteFixedLookupM1.rates := by
  unfold finiteFixedRatesQM1 FixedRationalLookup.rates
  congr 1 <;> funext i <;> fin_cases i <;> decide +kernel

theorem finiteFixedRatesQM1_toReal : finiteFixedRatesQM1.toReal = finiteFixedPrintedRates 1 := by
  rw [finiteFixedRatesQM1_eq_lookup]
  exact finiteFixedLookupM1_valid.rates_cast

theorem finiteFixedCoordinatesQM1_eq_lookup (j : Fin 3) :
    finiteFixedCoordinatesQM1 j = finiteFixedLookupM1.coordinate j := by
  apply Prod.ext
  · funext i
    fin_cases j <;> fin_cases i <;> decide +kernel
  · apply Prod.ext
    · funext i
      fin_cases j <;> fin_cases i <;> decide +kernel
    · funext i
      fin_cases j <;> fin_cases i <;> decide +kernel

theorem finiteFixedCoordinatesQM1_toReal (j : Fin 3) :
    (finiteFixedCoordinatesQM1 j).toReal =
      toCoordinateSpace (chart (finiteFixedPrintedState 1 j)) := by
  rw [finiteFixedCoordinatesQM1_eq_lookup]
  exact finiteFixedLookupM1_valid.coordinate_cast j

end
end PhosphorylationStableCapacity
