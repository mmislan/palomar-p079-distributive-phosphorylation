module
public import proofs.PhosphorylationStableCapacity.CoalescedCoefficientRatioOrder
public import proofs.PhosphorylationStableCapacity.CoalescedFeedbackSignReduction

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section

theorem coalescedOccupancyRatio_eq_coeff (m i : ℕ) (hi : i ≤ m + 1) :
    coalescedOccupancyRatio m i =
      (coalescedPair (m + 1)).2.coeff i /
        ((coalescedPair (m + 1)).1.coeff i +
          (coalescedPair (m + 1)).2.coeff i) := by
  have hden : (36 : ℝ) ^ (m + 1) ≠ 0 := by positivity
  have hsum : (coalescedPair (m + 1)).1.coeff i +
      (coalescedPair (m + 1)).2.coeff i ≠ 0 := by
    have hd := coalescedPair_dense (m + 1)
    exact ne_of_gt (add_pos (hd.1.1 i hi) (hd.2.1 i hi))
  unfold coalescedOccupancyRatio coalescedYNext coalescedLevelWeight
  field_simp [hden, hsum]

/-- The second source ratio premise of the conditional path-block theorem. -/
theorem coalescedOccupancyRatio_mono (m : ℕ) :
    ∀ i ≤ m,
      coalescedOccupancyRatio m i ≤
        coalescedOccupancyRatio m (i + 1) := by
  intro i hi
  have hd := coalescedPair_dense (m + 1)
  have hp0 := hd.1.1 i (by omega : i ≤ m + 1)
  have hp1 := hd.1.1 (i + 1) (by omega : i + 1 ≤ m + 1)
  have hq0 := hd.2.1 i (by omega : i ≤ m + 1)
  have hq1 := hd.2.1 (i + 1) (by omega : i + 1 ≤ m + 1)
  have hratio := coalescedJN_coeff_ratio_mono (m + 1) i (by omega)
  have hcross := (div_le_div_iff₀ hp0 hp1).1 hratio
  rw [coalescedOccupancyRatio_eq_coeff m i (by omega),
    coalescedOccupancyRatio_eq_coeff m (i + 1) (by omega)]
  apply (div_le_div_iff₀ (add_pos hp0 hq0) (add_pos hp1 hq1)).2
  nlinarith

theorem coalescedPath_block_hurwitz (m : ℕ) :
    IsHurwitz (fun i j =>
      -pathH (coalescedPathWeights m) i j +
        coalescedPathEdgeFeedback m j) := by
  exact coalescedPath_block_hurwitz_of_ratios m
    (coalescedPrevRatio_strict_mono m)
    (coalescedOccupancyRatio_mono m)

end
end PhosphorylationStableCapacity
