module
public import proofs.PhosphorylationStableCapacity.CoalescedJAllRoots

@[expose] public section

namespace PhosphorylationStableCapacity

/-- A single positive-root shift preserves the desired ordering of
corresponding coefficient ratios whenever the unchanged factor has
log-concave adjacent coefficients. -/
theorem factor_replacement_ratio_mono
    (a b qPrev qNow qNext : ℝ)
    (hba : b ≤ a)
    (hlog : qPrev * qNext ≤ qNow ^ 2)
    (hden0 : 0 < a * qNow + qPrev)
    (hden1 : 0 < a * qNext + qNow) :
    (b * qNow + qPrev) / (a * qNow + qPrev) ≤
      (b * qNext + qNow) / (a * qNext + qNow) := by
  apply (div_le_div_iff₀ hden0 hden1).2
  have hprod : 0 ≤ (a - b) * (qNow ^ 2 - qPrev * qNext) :=
    mul_nonneg (sub_nonneg.mpr hba) (sub_nonneg.mpr hlog)
  nlinarith [hprod]

end PhosphorylationStableCapacity
