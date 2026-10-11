module
public import Mathlib.Algebra.BigOperators.Field
public import proofs.PhosphorylationStableCapacity.CoalescedCoefficientMoments

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section

/-- The leading level mass used by the coalesced path block. The source
length is `m+1`, so the levels are indexed from zero through `m+1`. -/
def coalescedLevelWeight (m i : ℕ) : ℝ :=
  ((coalescedPair (m + 1)).1.coeff i +
    (coalescedPair (m + 1)).2.coeff i) / (36 : ℝ)^(m + 1)

theorem coalescedLevelWeight_pos (m i : ℕ) (hi : i ≤ m + 1) :
    0 < coalescedLevelWeight m i := by
  have hd := coalescedPair_dense (m + 1)
  unfold coalescedLevelWeight
  exact div_pos (add_pos (hd.1.1 i hi) (hd.2.1 i hi)) (by positivity)

theorem coalescedLevelWeight_mass (m : ℕ) :
    (∑ i ∈ Finset.range (m + 2), coalescedLevelWeight m i) = 2 := by
  have hs := coalescedPair_coeff_sums (m + 1)
  have hj : (36 : ℝ)^(m + 1) ≠ 0 := by positivity
  have hindex : m + 1 + 1 = m + 2 := by omega
  simp only [coalescedLevelWeight]
  rw [← Finset.sum_div, Finset.sum_add_distrib]
  rw [← hindex, hs.1, hs.2]
  field_simp
  norm_num

theorem coalescedLevelWeight_first_moment (m : ℕ) :
    (∑ i ∈ Finset.range (m + 2),
      coalescedLevelWeight m i * (i : ℝ)) =
        2 * ((4 * (m : ℝ) + 5) / 9) := by
  have hs := coalescedPair_coeff_first_moments m
  have hj : (36 : ℝ)^(m + 1) ≠ 0 := by positivity
  simp only [coalescedLevelWeight]
  simp_rw [div_mul_eq_mul_div, add_mul]
  rw [← Finset.sum_div, Finset.sum_add_distrib]
  rw [hs.1, hs.2]
  field_simp
  ring

end
end PhosphorylationStableCapacity
