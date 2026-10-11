module
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import proofs.PhosphorylationStableCapacity.RatioSubstrateFormula

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section
open PhosphorylationSharpness

/-- Explicit positive substrate level along the fixed-ratio profile,
for arbitrary positive rates and totals. -/
def modelRatioSubstrateLevel {n : ℕ}
    (k : Rates n) (FT ST u : ℝ) : ℝ :=
  ratioSubstrateFormula FT ST (freeSubstrateInventory k u)
    (kinaseComplexInventory k u + phosphataseComplexInventory k u)
    (phosphataseComplexInventory k u)

theorem modelRatioSubstrateLevel_pos_and_inventory {n : ℕ}
    (hn : 0 < n) (k : Rates n) (hk : k.Positive)
    (FT ST u : ℝ) (hST : 0 < ST) (hu : 0 < u) :
    0 < modelRatioSubstrateLevel k FT ST u ∧
      ratioSubstrateInventory FT (freeSubstrateInventory k u)
        (kinaseComplexInventory k u + phosphataseComplexInventory k u)
        (phosphataseComplexInventory k u)
        (modelRatioSubstrateLevel k FT ST u) = ST := by
  simpa only [modelRatioSubstrateLevel] using
    ratioSubstrateFormula_pos_and_inventory FT ST
      (freeSubstrateInventory k u)
      (kinaseComplexInventory k u + phosphataseComplexInventory k u)
      (phosphataseComplexInventory k u)
      hST (freeSubstrateInventory_pos k hk hu)
      (phosphataseComplexInventory_pos k hk hu hn)

theorem modelRatioSubstrateLevel_differentiableAt {n : ℕ}
    (hn : 0 < n) (k : Rates n) (hk : k.Positive)
    (FT ST u : ℝ) (hST : 0 < ST) (hu : 0 < u) :
    DifferentiableAt ℝ (modelRatioSubstrateLevel k FT ST) u := by
  have hT : 0 < freeSubstrateInventory k u :=
    freeSubstrateInventory_pos k hk hu
  have hD : 0 < phosphataseComplexInventory k u :=
    phosphataseComplexInventory_pos k hk hu hn
  unfold modelRatioSubstrateLevel ratioSubstrateFormula
  simp only [freeSubstrateInventory, kinaseComplexInventory,
    phosphataseComplexInventory]
  fun_prop (disch := positivity)

end
end PhosphorylationStableCapacity
