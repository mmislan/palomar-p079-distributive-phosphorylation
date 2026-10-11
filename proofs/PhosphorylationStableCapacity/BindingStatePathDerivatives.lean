module
public import proofs.PhosphorylationStableCapacity.LoadedReducedField

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section
open PhosphorylationSharpness

/-- The free-substrate component of the binding path is affine. -/
theorem bindingLinearPath_hasDerivAt {ι : Type*}
    (S σ : ι → ℝ) (i : ι) :
    HasDerivAt (fun t : ℝ => bindingLinearPath S σ t i)
      (S i * σ i) 0 := by
  have h := ((hasDerivAt_id (𝕜 := ℝ) (0 : ℝ)).const_mul
    (S i * σ i)).const_add (S i)
  convert h using 1
  · funext t
    simp only [bindingLinearPath, id_eq]
    ring
  · ring

/-- The free-enzyme component has a quotient derivative along the
binding path whenever the base binding denominator is nonzero. -/
theorem bindingFree_hasDerivAt_linearPath {ι : Type*} [Fintype ι]
    (ET : ℝ) (p S σ : ι → ℝ)
    (hden : bindingDenominator p S ≠ 0) :
    HasDerivAt (fun t : ℝ =>
      ET / bindingDenominator p (bindingLinearPath S σ t))
      (-(ET * bindingWeightedTangent p S σ) /
        (bindingDenominator p S) ^ 2) 0 := by
  have hfun : (fun t : ℝ =>
      ET / bindingDenominator p (bindingLinearPath S σ t)) =
      (fun t : ℝ =>
        (ET + 0 * t) /
          (bindingDenominator p S + bindingWeightedTangent p S σ * t)) := by
    funext t
    rw [bindingDenominator_linearPath]
    ring
  rw [hfun]
  convert hasDerivAt_affine_div ET 0
    (bindingDenominator p S) (bindingWeightedTangent p S σ)
    hden using 1
  ring

end
end PhosphorylationStableCapacity
