module
public import proofs.PhosphorylationStableCapacity.FiniteFixedRationalLookup

@[expose] public section

namespace PhosphorylationStableCapacity
noncomputable section

/-- Exact rational source coefficients for printed m=3. -/
def finiteFixedLookupM3 : FixedRationalLookup 3 where
  spacing := (1 : ℚ) / 2
  inventory := ![(1637874945 : ℚ) / 64, (726355431513 : ℚ) / 64, (225599025963 : ℚ) / 8, (18454330008 : ℚ), (1578163584 : ℚ)]
  binding := ![(1521174206475 : ℚ) / 64, (1771980942105 : ℚ) / 16, (73813328160 : ℚ), (294951360 : ℚ)]
  release := ![(1637874945 : ℚ) / 64, (90589694571 : ℚ) / 8, (16876166424 : ℚ), (1578163584 : ℚ)]
  coalescedRelease := ![(87146496 : ℚ), (14377844736 : ℚ), (18388353024 : ℚ), (1652686848 : ℚ)]

end
end PhosphorylationStableCapacity
