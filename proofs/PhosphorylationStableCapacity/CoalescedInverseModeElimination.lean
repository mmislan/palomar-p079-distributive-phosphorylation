module
public import proofs.PhosphorylationStableCapacity.CoalescedTwoModeBlock

@[expose] public section

namespace PhosphorylationStableCapacity

/-! The exact scalar elimination in equation (7) of the coalesced spectral
argument. The premise equations are the two mode equations (6). Deriving them
from the finite loaded mass inverse is a separate obligation. -/

theorem coalesced_inverse_mode_feedback
    {v T U a b : ℝ}
    (hv0 : 0 < v) (hv1 : v < 1)
    (hrow : (3 * T / 2 + U) + (7 - 3 * v) * a / 2 +
      3 * v * b / 2 = 0)
    (hlast : (4 - v) * b = T + (1 - v) * a) :
    2 * b - a = (10 * T + (2 + v) * U) / (2 * (7 - 4 * v)) := by
  have hden : 2 * (7 - 4 * v) ≠ 0 := by
    have hcore : 0 < 7 - 4 * v := by linarith
    have : 0 < 2 * (7 - 4 * v) := by positivity
    exact ne_of_gt this
  have hrow' : 3 * T + 2 * U + (7 - 3 * v) * a + 3 * v * b = 0 := by
    linear_combination 2 * hrow
  have hlast' : (4 - v) * b - T - (1 - v) * a = 0 := by
    linear_combination hlast
  have hcomb :
      2 * (7 - 4 * v) * (2 * b - a) = 10 * T + (2 + v) * U := by
    linear_combination (-(v + 2) / 2) * hrow' +
      ((14 - 3 * v) / 2) * hlast'
  apply (eq_div_iff hden).2
  calc
    (2 * b - a) * (2 * (7 - 4 * v)) =
        2 * (7 - 4 * v) * (2 * b - a) := by ring
    _ = 10 * T + (2 + v) * U := hcomb

end PhosphorylationStableCapacity
