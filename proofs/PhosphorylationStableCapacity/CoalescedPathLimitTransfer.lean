module
public import proofs.PhosphorylationStableCapacity.CoalescedPathStrictFeedback
public import proofs.PhosphorylationStableCapacity.MetzlerLimit

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section

def coalescedPathBlock (m : ℕ) : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ :=
  fun i j => -pathH (coalescedPathWeights m) i j +
    coalescedPathEdgeFeedback m j

/-- The all-size negative-action certificate for the literal source path
block, using the explicit positive path vector. -/
theorem coalescedPathBlock_negative_vector (m : ℕ) :
    ∀ i, ∑ j, coalescedPathBlock m i j *
      pathVectorFin (coalescedPathWeights m) j < 0 := by
  have hv := coalescedV_bounds m
  have hd := coalescedPathWeights_pos m
  have hH : ∀ i, ∑ j, pathH (coalescedPathWeights m) i j *
      pathVectorFin (coalescedPathWeights m) j = 1 := by
    intro i
    simpa only [Matrix.mulVec, dotProduct] using
      pathVectorFin_action (by omega : 0 < m + 1)
        (coalescedPathWeights m) hd i
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
  have hneg := large_r_block_certificate (m + 2) (by omega)
    (coalescedV m) hv.1 hv.2
    (pathH (coalescedPathWeights m)) (coalescedPathEdgeFeedback m)
    (pathVectorFin (coalescedPathWeights m)) hH hgain
  simpa [coalescedPathBlock, Nat.add_assoc] using hneg

/-- Once a parameterized loaded block is proved to converge entrywise to
the source path block, its matrices are eventually Hurwitz. This theorem
does not assert that a particular literal Jacobian block has that limit. -/
theorem coalescedPathBlock_eventually_hurwitz_of_entrywise_limit
    {α : Type*} {l : Filter α} (m : ℕ)
    (A : α → Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ)
    (hentry : ∀ i j,
      Filter.Tendsto (fun t => A t i j) l
        (nhds (coalescedPathBlock m i j))) :
    ∀ᶠ t in l, IsHurwitz (A t) := by
  apply eventually_hurwitz_of_entrywise_strict_metzler_limit
    A (coalescedPathBlock m) (pathVectorFin (coalescedPathWeights m))
  · exact pathVectorFin_pos (coalescedPathWeights m)
      (coalescedPathWeights_pos m)
  · exact hentry
  · intro i j hij
    exact coalescedPath_block_offdiag_pos m i j hij
  · exact coalescedPathBlock_negative_vector m

end
end PhosphorylationStableCapacity
