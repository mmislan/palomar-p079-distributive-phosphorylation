module
public import proofs.PhosphorylationStableCapacity.SplitEigenvalueAsymptoticBridge

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section

/-- A quantitative quotient estimate for the first-order error in the
splitting coefficient. The numerator is the exact determinant prefactor;
the denominator is the complementary characteristic factor. -/
theorem first_order_quotient_bound
    (a b a₀ b₀ A B t : ℝ)
    (hb₀ : 0 < b₀) (hb : b₀ / 2 ≤ b)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (ht : 0 ≤ t)
    (ha : |a - a₀| ≤ A * t)
    (hbb : |b - b₀| ≤ B * t) :
    |a / b - a₀ / b₀| ≤
      ((A * b₀ + |a₀| * B) * t) / (b₀ ^ 2 / 2) := by
  have hbpos : 0 < b := by linarith
  have hdenpos : 0 < b₀ ^ 2 / 2 := by positivity
  have hden : b₀ ^ 2 / 2 ≤ b * b₀ := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hb) hb₀.le]
  have hnum : |a * b₀ - a₀ * b| ≤ (A * b₀ + |a₀| * B) * t := by
    have hid : a * b₀ - a₀ * b = (a - a₀) * b₀ - a₀ * (b - b₀) := by ring
    rw [hid]
    calc
      |(a - a₀) * b₀ - a₀ * (b - b₀)| ≤
          |(a - a₀) * b₀| + |a₀ * (b - b₀)| := by
            simpa using abs_sub_le ((a-a₀)*b₀) 0 (a₀*(b-b₀))
      _ = |a - a₀| * b₀ + |a₀| * |b - b₀| := by
          rw [abs_mul, abs_mul, abs_of_pos hb₀]
      _ ≤ (A * b₀ + |a₀| * B) * t := by
          nlinarith [mul_nonneg (sub_nonneg.mpr ha) hb₀.le,
            mul_nonneg (sub_nonneg.mpr hbb) (abs_nonneg a₀)]
  have hcoef : 0 ≤ (A * b₀ + |a₀| * B) * t := by positivity
  have hident : a / b - a₀ / b₀ = (a * b₀ - a₀ * b) / (b * b₀) := by
    field_simp
  rw [hident, abs_div, abs_mul, abs_of_pos hbpos, abs_of_pos hb₀]
  calc
    |a * b₀ - a₀ * b| / (b * b₀) ≤
        ((A * b₀ + |a₀| * B) * t) / (b * b₀) := by
      gcongr
    _ ≤ ((A * b₀ + |a₀| * B) * t) / (b₀ ^ 2 / 2) := by
      gcongr

end
end PhosphorylationStableCapacity
