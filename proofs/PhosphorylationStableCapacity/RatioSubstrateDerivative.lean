module
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Inv
public import proofs.PhosphorylationStableCapacity.RatioSubstratePivot
public import Mathlib.Analysis.Calculus.Deriv.Basic

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section
open PhosphorylationSharpness

/-- The exact derivative of the fixed-ratio substrate inventory in
the level-zero substrate variable. Its denominator never vanishes
on the nonnegative profile when `D ≥ 0`. -/
theorem ratioSubstrateInventory_hasDerivAt
    (FT T K D s : ℝ) (hden : 1 + D * s ≠ 0) :
    HasDerivAt (ratioSubstrateInventory FT T K D)
      (T + FT * K / (1 + D * s) ^ 2) s := by
  have hid : HasDerivAt (fun t : ℝ => t) 1 s := hasDerivAt_id s
  have hlinear : HasDerivAt (fun t : ℝ => 1 + D * t) D s := by
    convert (hasDerivAt_const s (1 : ℝ)).add (hid.const_mul D) using 1; ring
  have hquot : HasDerivAt (fun t : ℝ => t / (1 + D * t))
      (1 / (1 + D * s) ^ 2) s := by
    convert hid.div hlinear hden using 1; ring
  have hfirst : HasDerivAt (fun t : ℝ => t * T) T s := by
    convert hid.mul_const T using 1; ring
  have hsecond : HasDerivAt
      (fun t : ℝ => (FT * K) * (t / (1 + D * t)))
      (FT * K / (1 + D * s) ^ 2) s := by
    convert hquot.const_mul (FT * K) using 1; ring
  have hfun : ratioSubstrateInventory FT T K D =
      (fun t : ℝ => t * T) +
        (fun t : ℝ => (FT * K) * (t / (1 + D * t))) := by
    funext t
    rfl
  rw [hfun]
  convert hfirst.add hsecond using 1

theorem ratioSubstrateInventory_deriv_pos
    (FT T K D s : ℝ)
    (hFT : 0 < FT) (hT : 0 < T) (hK : 0 < K)
    (hD : 0 ≤ D) (hs : 0 ≤ s) :
    0 < deriv (ratioSubstrateInventory FT T K D) s := by
  have hden : 0 < 1 + D * s := by nlinarith [mul_nonneg hD hs]
  rw [(ratioSubstrateInventory_hasDerivAt FT T K D s hden.ne').deriv]
  positivity

theorem model_ratio_substrate_inventory_deriv_pos {n : ℕ}
    (hn : 0 < n) (k : Rates n) (hk : k.Positive)
    (FT u s : ℝ) (hFT : 0 < FT) (hu : 0 < u) (hs : 0 ≤ s) :
    0 < deriv (ratioSubstrateInventory FT
      (freeSubstrateInventory k u)
      (kinaseComplexInventory k u + phosphataseComplexInventory k u)
      (phosphataseComplexInventory k u)) s := by
  exact ratioSubstrateInventory_deriv_pos FT
    (freeSubstrateInventory k u)
    (kinaseComplexInventory k u + phosphataseComplexInventory k u)
    (phosphataseComplexInventory k u) s
    hFT (freeSubstrateInventory_pos k hk hu)
    (add_pos (kinaseComplexInventory_pos k hk hu hn)
      (phosphataseComplexInventory_pos k hk hu hn))
    (phosphataseComplexInventory_pos k hk hu hn).le hs

end
end PhosphorylationStableCapacity
