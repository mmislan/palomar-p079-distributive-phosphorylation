module
public import proofs.PhosphorylationStableCapacity.CoalescedLevelWeight

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section

/-- Normalized leading phosphatase-complex level weight. -/
def coalescedYNext (m i : ℕ) : ℝ :=
  (coalescedPair (m + 1)).2.coeff i / (36 : ℝ)^(m + 1)

def coalescedV (m : ℕ) : ℝ := coalescedYNext m (m + 1)

def coalescedMu (m : ℕ) : ℝ := (4 * (m : ℝ) + 5) / 9

theorem coalescedV_bounds (m : ℕ) : 0 < coalescedV m ∧ coalescedV m < 1 := by
  have hd := coalescedPair_dense (m + 1)
  have hs := (coalescedPair_coeff_sums (m + 1)).2
  have hj : 0 < (36 : ℝ)^(m + 1) := by positivity
  have hpartial :
      0 < ∑ i ∈ Finset.range (m + 1),
        (coalescedPair (m + 1)).2.coeff i := by
    apply Finset.sum_pos
    · intro i hi
      exact hd.2.1 i (by have := Finset.mem_range.mp hi; omega)
    · exact ⟨0, by simp⟩
  have hindex : m + 1 + 1 = m + 2 := by omega
  have hsplit :
      (∑ i ∈ Finset.range (m + 2),
        (coalescedPair (m + 1)).2.coeff i) =
        (∑ i ∈ Finset.range (m + 1),
          (coalescedPair (m + 1)).2.coeff i) +
          (coalescedPair (m + 1)).2.coeff (m + 1) := by
    rw [← hindex, Finset.sum_range_succ]
  have hsum :
      (coalescedPair (m + 1)).2.coeff (m + 1) <
        (36 : ℝ)^(m + 1) := by
    rw [hindex] at hs
    linarith [hs, hsplit]
  constructor
  · exact div_pos (hd.2.1 (m + 1) (by omega)) hj
  · unfold coalescedV coalescedYNext
    exact (div_lt_one hj).mpr hsum

/-- The second source moment in the manuscript, prior to feedback scaling. -/
theorem coalescedYNext_centered_moment (m : ℕ) :
    (∑ i ∈ Finset.range (m + 2),
      coalescedYNext m i * ((i : ℝ) - coalescedMu m)) = 1 / 3 := by
  have hs := (coalescedPair_coeff_sums (m + 1)).2
  have hm := (coalescedPair_coeff_first_moments m).2
  have hj : (36 : ℝ)^(m + 1) ≠ 0 := by positivity
  have hindex : m + 1 + 1 = m + 2 := by omega
  rw [hindex] at hs
  simp only [coalescedYNext, div_mul_eq_mul_div]
  rw [← Finset.sum_div]
  simp_rw [mul_sub]
  rw [Finset.sum_sub_distrib, ← Finset.sum_mul]
  rw [hm, hs]
  unfold coalescedMu
  field_simp
  ring

end
end PhosphorylationStableCapacity
