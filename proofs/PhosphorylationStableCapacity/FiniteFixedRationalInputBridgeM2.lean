module
public import proofs.PhosphorylationStableCapacity.FiniteFixedRationalInputDataM2
public import proofs.PhosphorylationStableCapacity.FiniteFixedRationalLookupValidM2
public import Mathlib.Tactic.FinCases

@[expose] public section

namespace PhosphorylationStableCapacity
noncomputable section
open PhosphorylationSharpness
set_option maxHeartbeats 2000000
set_option maxRecDepth 8192

theorem finiteFixedRatesQM2_eq_lookup : finiteFixedRatesQM2 = finiteFixedLookupM2.rates := by
  unfold finiteFixedRatesQM2 FixedRationalLookup.rates
  congr 1 <;> funext i <;> fin_cases i <;> decide +kernel

theorem finiteFixedRatesQM2_toReal : finiteFixedRatesQM2.toReal = finiteFixedPrintedRates 2 := by
  rw [finiteFixedRatesQM2_eq_lookup]
  exact finiteFixedLookupM2_valid.rates_cast

theorem finiteFixedCoordinatesQM2_eq_lookup (j : Fin 5) :
    finiteFixedCoordinatesQM2 j = finiteFixedLookupM2.coordinate j := by
  apply Prod.ext
  · funext i
    fin_cases j <;> fin_cases i <;> decide +kernel
  · apply Prod.ext
    · funext i
      fin_cases j <;> fin_cases i <;> decide +kernel
    · funext i
      fin_cases j <;> fin_cases i <;> decide +kernel

theorem finiteFixedCoordinatesQM2_toReal (j : Fin 5) :
    (finiteFixedCoordinatesQM2 j).toReal =
      toCoordinateSpace (chart (finiteFixedPrintedState 2 j)) := by
  rw [finiteFixedCoordinatesQM2_eq_lookup]
  exact finiteFixedLookupM2_valid.coordinate_cast j

end
end PhosphorylationStableCapacity
