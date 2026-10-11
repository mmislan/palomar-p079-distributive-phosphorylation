module
public import proofs.PhosphorylationStableCapacity.BindingStateEnzymeTotals

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section
open PhosphorylationSharpness Filter

/-- With an absent terminal kinase complex, the literal kinase total has
zero derivative along a reversible-binding path through a point with
nonzero binding denominator. -/
theorem bindingState_totalE_path_hasDerivAt_zero {n : ℕ}
    (ET FT : ℝ) (p q S σ : Fin (n + 1) → ℝ)
    (hp : ∀ T : Fin (n + 1) → ℝ,
      bindingComplex ET p T (Fin.last n) = 0)
    (hden : bindingDenominator p S ≠ 0) :
    HasDerivAt (fun t : ℝ =>
      totalE (bindingState ET FT p q (bindingLinearPath S σ t))) 0 0 := by
  have hcont : ContinuousAt (fun t : ℝ =>
      bindingDenominator p (bindingLinearPath S σ t)) 0 := by
    have hfun : (fun t : ℝ =>
        bindingDenominator p (bindingLinearPath S σ t)) =
        (fun t : ℝ =>
          bindingDenominator p S + t * bindingWeightedTangent p S σ) := by
      funext t
      exact bindingDenominator_linearPath p S σ t
    rw [hfun]
    fun_prop
  have hne : ∀ᶠ t : ℝ in nhds (0 : ℝ),
      bindingDenominator p (bindingLinearPath S σ t) ≠ 0 :=
    hcont.eventually_ne (by
      have hzero : bindingLinearPath S σ 0 = S := by
        funext i
        simp [bindingLinearPath]
      simpa only [hzero] using hden)
  have heq : (fun t : ℝ =>
      totalE (bindingState ET FT p q (bindingLinearPath S σ t))) =ᶠ[nhds 0]
        (fun _ : ℝ => ET) := by
    filter_upwards [hne] with t ht
    exact bindingState_totalE ET FT p q _ (hp _) ht
  exact (hasDerivAt_const (0 : ℝ) ET).congr_of_eventuallyEq heq

/-- The same first-order conservation holds for the phosphatase total. -/
theorem bindingState_totalF_path_hasDerivAt_zero {n : ℕ}
    (ET FT : ℝ) (p q S σ : Fin (n + 1) → ℝ)
    (hq : ∀ T : Fin (n + 1) → ℝ,
      bindingComplex FT q T 0 = 0)
    (hden : bindingDenominator q S ≠ 0) :
    HasDerivAt (fun t : ℝ =>
      totalF (bindingState ET FT p q (bindingLinearPath S σ t))) 0 0 := by
  have hcont : ContinuousAt (fun t : ℝ =>
      bindingDenominator q (bindingLinearPath S σ t)) 0 := by
    have hfun : (fun t : ℝ =>
        bindingDenominator q (bindingLinearPath S σ t)) =
        (fun t : ℝ =>
          bindingDenominator q S + t * bindingWeightedTangent q S σ) := by
      funext t
      exact bindingDenominator_linearPath q S σ t
    rw [hfun]
    fun_prop
  have hne : ∀ᶠ t : ℝ in nhds (0 : ℝ),
      bindingDenominator q (bindingLinearPath S σ t) ≠ 0 :=
    hcont.eventually_ne (by
      have hzero : bindingLinearPath S σ 0 = S := by
        funext i
        simp [bindingLinearPath]
      simpa only [hzero] using hden)
  have heq : (fun t : ℝ =>
      totalF (bindingState ET FT p q (bindingLinearPath S σ t))) =ᶠ[nhds 0]
        (fun _ : ℝ => FT) := by
    filter_upwards [hne] with t ht
    exact bindingState_totalF ET FT p q _ (hq _) ht
  exact (hasDerivAt_const (0 : ℝ) FT).congr_of_eventuallyEq heq

end
end PhosphorylationStableCapacity
