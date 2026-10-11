module
public import proofs.PhosphorylationStableCapacity.FiniteFixedPrintedAllSpectra
public import proofs.PhosphorylationStableCapacity.FiniteFixedPrintedCoefficients
public import proofs.PhosphorylationStableCapacity.FiniteFixedPrintedContractAssembly

@[expose] public section

namespace PhosphorylationStableCapacity.P079PrintedContract

noncomputable section
open PhosphorylationSharpness

/-- Proposition 9.1's complete finite table: one common printed rational
system for each size, all positive equilibria exhausted, with the claimed
nonlinear sink and simple one-unstable saddle spectra on those same states. -/
theorem paper_fixed_finite_table : PaperFixedFiniteTable := by
  apply finiteFixedPrinted_contract_of_coefficients_and_spectra
  · intro m hm hm6
    exact finiteFixedPrinted_coefficients_positive m hm hm6
  · exact finiteFixedPrinted_all_spectra

end
end PhosphorylationStableCapacity.P079PrintedContract
