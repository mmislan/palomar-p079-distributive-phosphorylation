module
public import proofs.PhosphorylationStableCapacity.CoalescedPrefixEdgeBlockLimit

@[expose] public section

namespace PhosphorylationStableCapacity

open Filter PhosphorylationSharpness
open scoped Topology

noncomputable section

/-- The finite first-prefix catalytic-current derivative on the actual
inverse-response columns, with its positive current weights included. -/
def coalescedPrefixCurrentMatrix (m : ℕ) (r : ℝ) :
    Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ :=
  fun i j => coalescedScaledEdgeCurrent m r
    (coalescedPrefixEdgeForcing m j) i

/-- The current-weighted finite edge matrix converges entrywise to the
positive row scaling of the source path block. -/
theorem coalescedPrefixCurrentMatrix_tendsto (m : ℕ)
    (i j : Fin (m + 1)) :
    Tendsto (fun r : ℝ => coalescedPrefixCurrentMatrix m r i j)
      atTop (𝓝 (coalescedYNext m i.val *
        coalescedPathBlock m i j)) := by
  have hD : Tendsto (fun r : ℝ =>
      (coalescedFiniteState (m + 1) r).D i.castSucc)
      atTop (𝓝 (coalescedYNext m i.val)) := by
    simpa [coalescedYNext] using
      coalescedFiniteState_D_tendsto (m + 1) i.castSucc
  have hA := coalescedPrefixEdgeActionMatrix_tendsto m i j
  have h := hD.mul hA
  simpa only [coalescedPrefixCurrentMatrix,
    coalescedPrefixEdgeActionMatrix,
    coalescedScaledEdgeCurrent,
    coalescedNormalizedEdgeAction] using h

/-- The actual finite catalytic-current derivative matrix on the first
prefix is eventually Hurwitz. The spectral relation to the full class
Jacobian remains an independent singular-perturbation obligation. -/
theorem coalescedPrefixCurrentMatrix_eventually_hurwitz (m : ℕ) :
    ∀ᶠ r : ℝ in atTop, IsHurwitz (coalescedPrefixCurrentMatrix m r) := by
  let B : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ :=
    fun i j => coalescedYNext m i.val * coalescedPathBlock m i j
  let w := pathVectorFin (coalescedPathWeights m)
  apply eventually_hurwitz_of_entrywise_strict_metzler_limit
    (coalescedPrefixCurrentMatrix m) B w
    (pathVectorFin_pos (coalescedPathWeights m)
      (coalescedPathWeights_pos m))
  · intro i j
    exact coalescedPrefixCurrentMatrix_tendsto m i j
  · intro i j hij
    exact mul_pos (coalescedYNext_prefix_pos m i)
      (coalescedPath_block_offdiag_pos m i j hij)
  · intro i
    change (∑ j, coalescedYNext m i.val *
      coalescedPathBlock m i j * w j) < 0
    simp_rw [mul_assoc]
    rw [← Finset.mul_sum]
    exact mul_neg_of_pos_of_neg
      (coalescedYNext_prefix_pos m i)
      (coalescedPathBlock_negative_vector m i)

end
end PhosphorylationStableCapacity
