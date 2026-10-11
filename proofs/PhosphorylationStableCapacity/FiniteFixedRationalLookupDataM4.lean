module
public import proofs.PhosphorylationStableCapacity.FiniteFixedRationalLookup

@[expose] public section

namespace PhosphorylationStableCapacity
noncomputable section

/-- Exact rational source coefficients for printed m=4. -/
def finiteFixedLookupM4 : FixedRationalLookup 4 where
  spacing := (1 : ℚ) / 4
  inventory := ![(24210781654838625 : ℚ) / 262144, (28322073063382491225 : ℚ) / 262144, (14433962053434340095 : ℚ) / 32768, (513186915159644005 : ℚ) / 1024, (709493080624965 : ℚ) / 4, (8755960070480 : ℚ)]
  binding := ![(115298027485775827875 : ℚ) / 262144, (192673109659169189925 : ℚ) / 65536, (1134171066406063455 : ℚ) / 256, (11444447720160105 : ℚ) / 8, (28630772010960 : ℚ)]
  release := ![(24210781654838625 : ℚ) / 262144, (3537232785215956575 : ℚ) / 32768, (340522789631824485 : ℚ) / 1024, (674469240343045 : ℚ) / 4, (8755960070480 : ℚ)]
  coalescedRelease := ![(157684596736 : ℚ), (122840549949440 : ℚ), (356366316208128 : ℚ), (173271299391488 : ℚ), (8890989150208 : ℚ)]

end
end PhosphorylationStableCapacity
