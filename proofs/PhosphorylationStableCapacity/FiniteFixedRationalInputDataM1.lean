module
public import proofs.PhosphorylationStableCapacity.FiniteRationalJacobianAction

@[expose] public section

namespace PhosphorylationStableCapacity
noncomputable section
open PhosphorylationSharpness

/-- Exact Q rates shared by all 3 printed m=1 states. -/
def finiteFixedRatesQM1 : RationalSiteRates 2 where
  a := ![(19782 : ℚ) / 1375, (311808 : ℚ) / 192049]
  b := ![(1 : ℚ), (1 : ℚ)]
  c := ![(625 : ℚ) / 1573, (4065 : ℚ) / 2431]
  alpha := ![(147000 : ℚ) / 124267, (79 : ℚ) / 34]
  beta := ![(1 : ℚ), (1 : ℚ)]
  gamma := ![(45 : ℚ) / 11, (45 : ℚ) / 34]

/-- Grouped exact Q chart coordinates for the m=1 family. -/
def finiteFixedCoordinatesQM1 : Fin 3 → RationalSiteCoordinate 2 := ![
  (![(1027 : ℚ) / 1008, (271 : ℚ) / 528], (![(39 : ℚ) / 14, (13 : ℚ) / 28], ![(125 : ℚ) / 462, (271 : ℚ) / 462])),
  (![(1 : ℚ), (8672 : ℚ) / 11297], (![(189 : ℚ) / 79, (48 : ℚ) / 79], ![(2625 : ℚ) / 11297, (8672 : ℚ) / 11297])),
  (![(869 : ℚ) / 912, (4065 : ℚ) / 3952], (![(77 : ℚ) / 38, (55 : ℚ) / 76], ![(875 : ℚ) / 4446, (1355 : ℚ) / 1482]))
]

end
end PhosphorylationStableCapacity
