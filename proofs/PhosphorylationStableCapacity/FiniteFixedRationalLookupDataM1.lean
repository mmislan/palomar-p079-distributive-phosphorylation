module
public import proofs.PhosphorylationStableCapacity.FiniteFixedRationalLookup

@[expose] public section

namespace PhosphorylationStableCapacity
noncomputable section

/-- Exact rational source coefficients for printed m=1. -/
def finiteFixedLookupM1 : FixedRationalLookup 1 where
  spacing := (1 : ℚ) / 2
  inventory := ![(2625 : ℚ) / 4, (11297 : ℚ) / 4, (2168 : ℚ)]
  binding := ![(27027 : ℚ) / 4, (1716 : ℚ)]
  release := ![(2625 : ℚ) / 4, (2168 : ℚ)]
  coalescedRelease := ![(704 : ℚ), (2176 : ℚ)]

end
end PhosphorylationStableCapacity
