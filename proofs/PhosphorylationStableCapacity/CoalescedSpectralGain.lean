module
public import proofs.PhosphorylationStableCapacity.CoalescedPathGain

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section

def coalescedPathEdgeFeedback (m : ℕ) : Fin (m + 1) → ℝ :=
  (pathIncidence (m + 1)).mulVec (coalescedPathFeedback m)

/-- The scalar gain, positive path test vector and source weights are all
discharged. The edge-feedback sign remains an explicit hypothesis. -/
theorem coalescedPath_block_hurwitz_of_edge_nonneg (m : ℕ)
    (hf : ∀ i, 0 ≤ coalescedPathEdgeFeedback m i) :
    IsHurwitz (fun i j =>
      -pathH (coalescedPathWeights m) i j +
        coalescedPathEdgeFeedback m j) := by
  have hv := coalescedV_bounds m
  have hd : ∀ i, 0 < coalescedPathWeights m i :=
    coalescedPathWeights_pos m
  have hgain :
      (∑ j, coalescedPathEdgeFeedback m j *
        pathVectorFin (coalescedPathWeights m) j) =
      (10 * ((4 : ℝ) / 3 - coalescedV m *
        (((m + 2 : ℕ) : ℝ) -
          (4 * ((m + 2 : ℕ) : ℝ) - 3) / 9)) +
          (2 + coalescedV m) / 3) / (14 - 8 * coalescedV m) := by
    unfold coalescedPathEdgeFeedback
    rw [coalescedPath_feedback_gain]
    unfold coalescedMu
    push_cast
    ring
  exact path_block_hurwitz_of_explicit_gain (m + 2) (by omega)
    (coalescedV m) hv.1 hv.2
    (coalescedPathWeights m) hd (coalescedPathEdgeFeedback m) hf hgain

end
end PhosphorylationStableCapacity
