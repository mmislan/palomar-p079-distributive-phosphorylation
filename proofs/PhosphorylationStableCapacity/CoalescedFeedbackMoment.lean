module
public import proofs.PhosphorylationStableCapacity.CoalescedYPrev

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section

/-- The source coefficient formula for the coalesced level feedback. -/
def coalescedFeedbackLevel (m i : ℕ) : ℝ :=
  (10 * coalescedYPrev m i +
    (2 + coalescedV m) * coalescedYNext m i) /
    (2 * (7 - 4 * coalescedV m) * coalescedLevelWeight m i)

/-- The exact source-specific feedback moment before converting levels to
edge differences. This is equation (9)'s scalar gain. -/
theorem coalescedFeedbackLevel_moment (m : ℕ) :
    (∑ i ∈ Finset.range (m + 2),
      coalescedFeedbackLevel m i * coalescedLevelWeight m i *
        ((i : ℝ) - coalescedMu m)) =
      (10 * (4 / 3 - coalescedV m *
        (((m : ℝ) + 2) - coalescedMu m)) +
          (2 + coalescedV m) / 3) / (14 - 8 * coalescedV m) := by
  have hv := (coalescedV_bounds m).2
  have hden : 2 * (7 - 4 * coalescedV m) ≠ 0 := by linarith
  have hterm (i : ℕ) (hi : i ∈ Finset.range (m + 2)) :
      coalescedFeedbackLevel m i * coalescedLevelWeight m i *
        ((i : ℝ) - coalescedMu m) =
        ((10 * coalescedYPrev m i +
          (2 + coalescedV m) * coalescedYNext m i) *
          ((i : ℝ) - coalescedMu m)) /
          (2 * (7 - 4 * coalescedV m)) := by
    have hd : coalescedLevelWeight m i ≠ 0 :=
      ne_of_gt (coalescedLevelWeight_pos m i
        (by have := Finset.mem_range.mp hi; omega))
    unfold coalescedFeedbackLevel
    field_simp [hd, hden]
  calc
    (∑ i ∈ Finset.range (m + 2),
      coalescedFeedbackLevel m i * coalescedLevelWeight m i *
        ((i : ℝ) - coalescedMu m)) =
      ∑ i ∈ Finset.range (m + 2),
        ((10 * coalescedYPrev m i +
          (2 + coalescedV m) * coalescedYNext m i) *
          ((i : ℝ) - coalescedMu m)) /
          (2 * (7 - 4 * coalescedV m)) := by
        apply Finset.sum_congr rfl
        exact hterm
    _ = (10 * (∑ i ∈ Finset.range (m + 2),
            coalescedYPrev m i * ((i : ℝ) - coalescedMu m)) +
          (2 + coalescedV m) * (∑ i ∈ Finset.range (m + 2),
            coalescedYNext m i * ((i : ℝ) - coalescedMu m))) /
          (2 * (7 - 4 * coalescedV m)) := by
        rw [← Finset.sum_div]
        congr 1
        calc
          (∑ i ∈ Finset.range (m + 2),
            (10 * coalescedYPrev m i +
              (2 + coalescedV m) * coalescedYNext m i) *
              ((i : ℝ) - coalescedMu m)) =
            ∑ i ∈ Finset.range (m + 2),
              (10 * (coalescedYPrev m i * ((i : ℝ) - coalescedMu m)) +
                (2 + coalescedV m) *
                  (coalescedYNext m i * ((i : ℝ) - coalescedMu m))) := by
              apply Finset.sum_congr rfl
              intro i hi
              ring
          _ = _ := by
            rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    _ = _ := by
      rw [coalescedYPrev_centered_moment_range,
        coalescedYNext_centered_moment]
      ring

end
end PhosphorylationStableCapacity
