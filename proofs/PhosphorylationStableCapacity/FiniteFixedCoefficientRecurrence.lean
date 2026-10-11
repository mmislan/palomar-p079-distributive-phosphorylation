module
public import proofs.PhosphorylationStableCapacity.FiniteFixedCoefficientBridge

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section
open PhosphorylationSharpness Polynomial

/-- Exact finite checker interface for the converted D coefficients. The
recurrence avoids evaluating polynomial long division in each printed case. -/
theorem finiteRawD_coeff_zero (p q : ℝ[X]) (r : ℝ) (hr : r ≠ 0) :
    (rawD p q r).coeff 0 = 4 * p.eval r * q.coeff 0 := by
  simp only [rawD, coeff_C_mul]
  rw [quotient_zero p q hr]
  ring

theorem finiteRawD_coeff_succ (p q : ℝ[X]) (r : ℝ) (hr : r ≠ 0)
    (i : ℕ) :
    (rawD p q r).coeff (i + 1) =
      4 * p.eval r * q.coeff (i + 1) +
        ((rawD p q r).coeff i - 4 * q.eval r * p.coeff i) / r := by
  simp only [rawD, coeff_C_mul]
  rw [quotient_succ p q hr i]
  ring

theorem finiteRawB_coeff (p q : ℝ[X]) (r : ℝ) (i : ℕ) :
    (rawB p q r).coeff i =
      r * (rawD p q r).coeff i +
        (4 * r * p.eval r - 2 * q.eval r) * p.coeff i -
          2 * q.eval r * q.coeff i := by
  simp only [rawB, coeff_add, coeff_sub, coeff_C_mul]

end
end PhosphorylationStableCapacity
