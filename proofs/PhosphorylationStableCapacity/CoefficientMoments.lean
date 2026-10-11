module
public import proofs.PhosphorylationStableCapacity.CoalescedMomentInduction

@[expose] public section

namespace PhosphorylationStableCapacity

open Polynomial

noncomputable section

theorem eval_one_eq_coeff_sum (p : ℝ[X]) (m : ℕ)
    (hdeg : p.natDegree ≤ m) :
    p.eval 1 = ∑ i ∈ Finset.range (m + 1), p.coeff i := by
  have hlt : p.natDegree < m + 1 := by omega
  simpa only [one_pow, mul_one] using
    (Polynomial.eval_eq_sum_range' hlt (1 : ℝ))

theorem derivative_eval_one_eq_coeff_moment (p : ℝ[X]) (m : ℕ)
    (hdeg : p.natDegree ≤ m) :
    (derivative p).eval 1 =
      ∑ i ∈ Finset.range (m + 1), p.coeff i * (i : ℝ) := by
  have hddeg : (derivative p).natDegree < m + 1 := by
    have h := Polynomial.natDegree_derivative_le p
    omega
  have htop : p.coeff (m + 1) = 0 :=
    Polynomial.natDegree_le_iff_coeff_eq_zero.mp hdeg (m + 1) (by omega)
  rw [Polynomial.eval_eq_sum_range' hddeg (1 : ℝ)]
  simp only [one_pow, mul_one, Polynomial.coeff_derivative]
  rw [Finset.sum_range_succ]
  simp only [htop, zero_mul, add_zero]
  rw [Finset.sum_range_succ']
  simp

end
end PhosphorylationStableCapacity
