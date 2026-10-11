module
public import proofs.PhosphorylationStableCapacity.CoalescedInverseModeElimination

@[expose] public section

namespace PhosphorylationStableCapacity

/-! The two remaining kernel-mode equations of the row-replacement system
have no nonzero homogeneous solution when the source top weight lies in
`(0,1)`. This is the mode part of its limiting invertibility proof. -/

theorem coalesced_mode_homogeneous_unique
    {v a b : ℝ} (hv0 : 0 < v) (hv1 : v < 1)
    (hrow : (7 - 3 * v) * a / 2 + 3 * v * b / 2 = 0)
    (hlast : (4 - v) * b = (1 - v) * a) :
    a = 0 ∧ b = 0 := by
  have hfeedback := coalesced_inverse_mode_feedback
    hv0 hv1 (T := 0) (U := 0) (by simpa using hrow)
    (by simpa using hlast)
  have hrelation : a = 2 * b := by
    norm_num at hfeedback
    linarith
  have hb : b = 0 := by
    rw [hrelation] at hlast
    have hcoef : 0 < 2 + v := by linarith
    nlinarith
  exact ⟨by rw [hrelation, hb]; ring, hb⟩

end PhosphorylationStableCapacity
