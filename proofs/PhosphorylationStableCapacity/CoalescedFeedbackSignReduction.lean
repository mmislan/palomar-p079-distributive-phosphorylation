module
public import proofs.PhosphorylationStableCapacity.CoalescedSpectralGain

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section

def coalescedPrevRatio (m i : ℕ) : ℝ :=
  coalescedYPrev m i / coalescedYNext m i

def coalescedOccupancyRatio (m i : ℕ) : ℝ :=
  coalescedYNext m i / coalescedLevelWeight m i

theorem coalescedYNext_pos (m i : ℕ) (hi : i ≤ m + 1) :
    0 < coalescedYNext m i := by
  have hd := (coalescedPair_dense (m + 1)).2.1 i hi
  exact div_pos hd (by positivity)

theorem coalescedYPrev_nonneg (m i : ℕ) (hi : i ≤ m + 1) :
    0 ≤ coalescedYPrev m i := by
  by_cases hzero : i = 0
  · simp [coalescedYPrev, hzero]
  · have hprev : i - 1 ≤ m + 1 := by omega
    simp only [coalescedYPrev, hzero, ite_false]
    exact (coalescedYNext_pos m (i - 1) hprev).le

theorem coalescedFeedbackLevel_factor (m i : ℕ) (hi : i ≤ m + 1) :
    coalescedFeedbackLevel m i =
      ((10 * coalescedPrevRatio m i + (2 + coalescedV m)) *
        coalescedOccupancyRatio m i) /
        (2 * (7 - 4 * coalescedV m)) := by
  have hy : coalescedYNext m i ≠ 0 :=
    ne_of_gt (coalescedYNext_pos m i hi)
  have hd : coalescedLevelWeight m i ≠ 0 :=
    ne_of_gt (coalescedLevelWeight_pos m i hi)
  have hv := (coalescedV_bounds m).2
  have hk : 2 * (7 - 4 * coalescedV m) ≠ 0 := by linarith
  unfold coalescedFeedbackLevel coalescedPrevRatio coalescedOccupancyRatio
  field_simp [hy, hd, hk]

/-- The ordinary coefficient route is reduced to its two exact ratio
inequalities. These remain mathematical hypotheses here. -/
theorem coalescedFeedbackLevel_strict_mono_of_ratios (m i : ℕ) (hi : i ≤ m)
    (hprev : coalescedPrevRatio m i < coalescedPrevRatio m (i + 1))
    (hoccupancy : coalescedOccupancyRatio m i ≤
      coalescedOccupancyRatio m (i + 1)) :
    coalescedFeedbackLevel m i < coalescedFeedbackLevel m (i + 1) := by
  have hii : i ≤ m + 1 := by omega
  have hij : i + 1 ≤ m + 1 := by omega
  have ha : 0 ≤ coalescedPrevRatio m i :=
    div_nonneg (coalescedYPrev_nonneg m i hii)
      (coalescedYNext_pos m i hii).le
  have hp : 0 < coalescedOccupancyRatio m i :=
    div_pos (coalescedYNext_pos m i hii)
      (coalescedLevelWeight_pos m i hii)
  have hprod := feedback_ratio_step
    (coalescedPrevRatio m i) (coalescedPrevRatio m (i + 1))
    (coalescedOccupancyRatio m i)
    (coalescedOccupancyRatio m (i + 1)) (coalescedV m)
    ha hprev hp hoccupancy (coalescedV_bounds m).1
  have hk : 0 < 2 * (7 - 4 * coalescedV m) := by
    have hv := (coalescedV_bounds m).2
    linarith
  rw [coalescedFeedbackLevel_factor m i hii,
    coalescedFeedbackLevel_factor m (i + 1) hij]
  exact div_lt_div_of_pos_right hprod hk

theorem coalescedPath_edge_nonneg_of_ratios (m : ℕ)
    (hprev : ∀ i ≤ m,
      coalescedPrevRatio m i < coalescedPrevRatio m (i + 1))
    (hoccupancy : ∀ i ≤ m,
      coalescedOccupancyRatio m i ≤
        coalescedOccupancyRatio m (i + 1)) :
    ∀ i, 0 ≤ coalescedPathEdgeFeedback m i := by
  intro i
  unfold coalescedPathEdgeFeedback
  rw [pathIncidence_mulVec]
  change 0 ≤ coalescedFeedbackLevel m (i.val + 1) -
    coalescedFeedbackLevel m i.val
  apply sub_nonneg.mpr
  exact (coalescedFeedbackLevel_strict_mono_of_ratios m i.val
    (by have := i.isLt; omega) (hprev i.val (by have := i.isLt; omega))
    (hoccupancy i.val (by have := i.isLt; omega))).le

theorem coalescedPath_block_hurwitz_of_ratios (m : ℕ)
    (hprev : ∀ i ≤ m,
      coalescedPrevRatio m i < coalescedPrevRatio m (i + 1))
    (hoccupancy : ∀ i ≤ m,
      coalescedOccupancyRatio m i ≤
        coalescedOccupancyRatio m (i + 1)) :
    IsHurwitz (fun i j =>
      -pathH (coalescedPathWeights m) i j +
        coalescedPathEdgeFeedback m j) := by
  exact coalescedPath_block_hurwitz_of_edge_nonneg m
    (coalescedPath_edge_nonneg_of_ratios m hprev hoccupancy)

end
end PhosphorylationStableCapacity
