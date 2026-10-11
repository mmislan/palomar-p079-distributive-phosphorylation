module
public import proofs.PhosphorylationStableCapacity.CoalescedPrevRatioMonotonicity

@[expose] public section

namespace PhosphorylationStableCapacity

/-- Monotone coefficient ratios survive multiplication of both polynomials
by the same positive linear factor. The three cross-product premises are the
adjacent and two-step ratio inequalities for the unchanged pair. -/
theorem common_factor_ratio_mono
    (r pPrev pNow pNext qPrev qNow qNext : ℝ)
    (hr : 0 ≤ r)
    (hleft : qPrev * pNow ≤ qNow * pPrev)
    (hmiddle : qPrev * pNext ≤ qNext * pPrev)
    (hright : qNow * pNext ≤ qNext * pNow)
    (hden0 : 0 < r * pNow + pPrev)
    (hden1 : 0 < r * pNext + pNow) :
    (r * qNow + qPrev) / (r * pNow + pPrev) ≤
      (r * qNext + qNow) / (r * pNext + pNow) := by
  apply (div_le_div_iff₀ hden0 hden1).2
  have h₁ : 0 ≤ r ^ 2 * (qNext * pNow - qNow * pNext) :=
    mul_nonneg (sq_nonneg r) (sub_nonneg.mpr hright)
  have h₂ : 0 ≤ r * (qNext * pPrev - qPrev * pNext) :=
    mul_nonneg hr (sub_nonneg.mpr hmiddle)
  have h₃ : 0 ≤ qNow * pPrev - qPrev * pNow :=
    sub_nonneg.mpr hleft
  nlinarith [h₁, h₂, h₃]

end PhosphorylationStableCapacity
