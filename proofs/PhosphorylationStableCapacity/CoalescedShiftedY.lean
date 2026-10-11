module
public import proofs.PhosphorylationStableCapacity.CoalescedYMoments

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section

theorem coalescedYNext_mass (m : ℕ) :
    (∑ i ∈ Finset.range (m + 2), coalescedYNext m i) = 1 := by
  have hs := (coalescedPair_coeff_sums (m + 1)).2
  have hj : (36 : ℝ)^(m + 1) ≠ 0 := by positivity
  have hindex : m + 1 + 1 = m + 2 := by omega
  rw [hindex] at hs
  simp only [coalescedYNext]
  rw [← Finset.sum_div, hs]
  exact div_self hj

/-- The first source moment in the manuscript, expressed with the preceding
level index. The term at level zero is zero, so this is the `y_i` moment. -/
theorem coalescedYPrev_centered_moment (m : ℕ) :
    (∑ i ∈ Finset.range (m + 1),
      coalescedYNext m i * (((i : ℝ) + 1) - coalescedMu m)) =
        4 / 3 - coalescedV m * (((m : ℝ) + 2) - coalescedMu m) := by
  have hindex : m + 1 + 1 = m + 2 := by omega
  have hsplitMass :
      (∑ i ∈ Finset.range (m + 2), coalescedYNext m i) =
        (∑ i ∈ Finset.range (m + 1), coalescedYNext m i) +
          coalescedV m := by
    unfold coalescedV
    rw [← hindex, Finset.sum_range_succ]
  have hpartialMass :
      (∑ i ∈ Finset.range (m + 1), coalescedYNext m i) =
        1 - coalescedV m := by
    linarith [coalescedYNext_mass m, hsplitMass]
  have hsplitMoment :
      (∑ i ∈ Finset.range (m + 2),
        coalescedYNext m i * ((i : ℝ) - coalescedMu m)) =
      (∑ i ∈ Finset.range (m + 1),
        coalescedYNext m i * ((i : ℝ) - coalescedMu m)) +
        coalescedV m * (((m + 1 : ℕ) : ℝ) - coalescedMu m) := by
    unfold coalescedV
    rw [← hindex, Finset.sum_range_succ]
  have hpartialMoment :
      (∑ i ∈ Finset.range (m + 1),
        coalescedYNext m i * ((i : ℝ) - coalescedMu m)) =
      1 / 3 - coalescedV m * (((m + 1 : ℕ) : ℝ) - coalescedMu m) := by
    linarith [coalescedYNext_centered_moment m, hsplitMoment]
  calc
    (∑ i ∈ Finset.range (m + 1),
      coalescedYNext m i * (((i : ℝ) + 1) - coalescedMu m)) =
        ∑ i ∈ Finset.range (m + 1),
          (coalescedYNext m i * ((i : ℝ) - coalescedMu m) +
            coalescedYNext m i) := by
        apply Finset.sum_congr rfl
        intro i hi
        ring
    _ = (∑ i ∈ Finset.range (m + 1),
          coalescedYNext m i * ((i : ℝ) - coalescedMu m)) +
          (∑ i ∈ Finset.range (m + 1), coalescedYNext m i) :=
        Finset.sum_add_distrib
    _ = 4 / 3 - coalescedV m * (((m : ℝ) + 2) - coalescedMu m) := by
      rw [hpartialMoment, hpartialMass]
      push_cast
      ring

end
end PhosphorylationStableCapacity
