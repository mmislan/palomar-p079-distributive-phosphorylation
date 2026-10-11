module
public import proofs.PhosphorylationStableCapacity.FiniteFixedRationalLookup

@[expose] public section

namespace PhosphorylationStableCapacity
noncomputable section

/-- Exact rational source coefficients for printed m=2. -/
def finiteFixedLookupM2 : FixedRationalLookup 2 where
  spacing := (1 : ℚ) / 2
  inventory := ![(790065 : ℚ) / 4, (37517481 : ℚ) / 4, (11830750 : ℚ), (2648896 : ℚ)]
  binding := ![(93618315 : ℚ) / 4, (56298693 : ℚ), (4494592 : ℚ)]
  release := ![(790065 : ℚ) / 4, (9181854 : ℚ), (2648896 : ℚ)]
  coalescedRelease := ![(285696 : ℚ), (9713664 : ℚ), (2691072 : ℚ)]

end
end PhosphorylationStableCapacity
