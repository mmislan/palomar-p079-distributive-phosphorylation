module
public import proofs.PhosphorylationStableCapacity.CoalescedDerivative

@[expose] public section

namespace PhosphorylationStableCapacity

open Polynomial

noncomputable section

/-- Exact all-size differentiated values for the literal equal-root source.
The base starts at one pair; the zero-pair seed has different ratios. -/
theorem coalescedPair_deriv_eval_one (m : ℕ) :
    (derivative (coalescedPair (m + 1)).1).eval 1 =
      (36 : ℝ)^(m + 1) * ((4 * (m : ℝ) + 2) / 9) ∧
    (derivative (coalescedPair (m + 1)).2).eval 1 =
      (36 : ℝ)^(m + 1) * ((4 * (m : ℝ) + 8) / 9) := by
  induction m with
  | zero =>
      constructor
      · change (derivative (PhosphorylationSharpness.nextN 3 3 (1 : ℝ[X]) 1)).eval 1 = _
        rw [nextN_33_deriv_eval_one]
        norm_num
      · change (derivative (PhosphorylationSharpness.nextJ 3 3 (1 : ℝ[X]) 1)).eval 1 = _
        rw [nextJ_33_deriv_eval_one]
        norm_num
  | succ m ih =>
      have heval := coalescedPair_eval_one (m + 1)
      constructor
      · change (derivative (PhosphorylationSharpness.nextN 3 3
          (coalescedPair (m + 1)).1 (coalescedPair (m + 1)).2)).eval 1 = _
        rw [nextN_33_deriv_eval_one, ih.1, ih.2, heval.1]
        push_cast
        simp only [pow_succ]
        ring
      · change (derivative (PhosphorylationSharpness.nextJ 3 3
          (coalescedPair (m + 1)).1 (coalescedPair (m + 1)).2)).eval 1 = _
        rw [nextJ_33_deriv_eval_one, ih.1, ih.2, heval.1, heval.2]
        push_cast
        simp only [pow_succ]
        ring

end
end PhosphorylationStableCapacity
