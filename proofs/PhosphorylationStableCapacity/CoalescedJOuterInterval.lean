module
public import proofs.PhosphorylationStableCapacity.CoalescedJInterlacingIntervals

@[expose] public section

namespace PhosphorylationStableCapacity

open Polynomial

noncomputable section

theorem coalescedJ_eval_zero_pos (m : ℕ) :
    0 < (coalescedPair m).2.eval 0 := by
  rw [← Polynomial.coeff_zero_eq_eval_zero]
  exact (coalescedPair_dense m).2.1 0 (Nat.zero_le m)

/-- The final companion root lies between the rightmost numerator root
and the origin. -/
theorem coalescedJ_zero_above_first_N_root (m : ℕ) (hm : 0 < m) :
    ∃ x : ℝ,
      coalescedRoot m 0 < x ∧ x < 0 ∧
        (coalescedPair m).2.eval x = 0 := by
  have hj0 : 0 < m := hm
  have hsign := coalescedJ_at_N_root_alternating m 0 hj0
  have hneg : (coalescedPair m).2.eval (coalescedRoot m 0) < 0 := by
    norm_num at hsign
    linarith
  exact polynomial_zero_between_of_opposite
    (coalescedRoot_neg m 0 hj0)
    (mul_neg_of_neg_of_pos hneg (coalescedJ_eval_zero_pos m))

end
end PhosphorylationStableCapacity
