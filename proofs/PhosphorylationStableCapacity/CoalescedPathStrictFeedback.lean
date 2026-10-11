module
public import proofs.PhosphorylationStableCapacity.CoalescedOccupancyRatioMonotonicity

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section

/-- Every adjacent source feedback difference is strictly positive. -/
theorem coalescedPathEdgeFeedback_pos (m : ℕ) (i : Fin (m + 1)) :
    0 < coalescedPathEdgeFeedback m i := by
  unfold coalescedPathEdgeFeedback
  rw [pathIncidence_mulVec]
  change 0 < coalescedFeedbackLevel m (i.val + 1) -
    coalescedFeedbackLevel m i.val
  apply sub_pos.mpr
  exact coalescedFeedbackLevel_strict_mono_of_ratios m i.val
    (by have := i.isLt; omega)
    (coalescedPrevRatio_strict_mono m i.val (by have := i.isLt; omega))
    (coalescedOccupancyRatio_mono m i.val (by have := i.isLt; omega))

/-- The source coalesced path block has strictly positive off-diagonal
entries, including edges that are not neighbors in the path Laplacian. -/
theorem coalescedPath_block_offdiag_pos (m : ℕ)
    (i j : Fin (m + 1)) (hij : i ≠ j) :
    0 < -pathH (coalescedPathWeights m) i j +
      coalescedPathEdgeFeedback m j := by
  have hd := coalescedPathWeights_pos m
  have hH := pathH_offdiag_nonpos (coalescedPathWeights m) hd i j hij
  have hf := coalescedPathEdgeFeedback_pos m j
  linarith

end
end PhosphorylationStableCapacity
