module
public import Mathlib.Algebra.Polynomial.Derivative
public import proofs.PhosphorylationStableCapacity.CoalescedMoments

@[expose] public section

namespace PhosphorylationStableCapacity

open PhosphorylationSharpness Polynomial

noncomputable section

/-- Differentiated equal-root source recurrence for the N polynomial. -/
theorem nextN_33_deriv_eval_one (p q : ℝ[X]) :
    (derivative (nextN 3 3 p q)).eval 1 =
      24 * (derivative p).eval 1 + 12 * (derivative q).eval 1 + 8 * p.eval 1 := by
  simp [nextN, derivative_add, derivative_mul]
  ring

/-- Differentiated equal-root source recurrence for the J polynomial. -/
theorem nextJ_33_deriv_eval_one (p q : ℝ[X]) :
    (derivative (nextJ 3 3 p q)).eval 1 =
      24 * (derivative p).eval 1 + 12 * (derivative q).eval 1 +
        24 * p.eval 1 + 8 * q.eval 1 := by
  simp [nextJ, derivative_add, derivative_mul]
  ring

end
end PhosphorylationStableCapacity
