module
public import proofs.PhosphorylationStableCapacity.CoalescedPrefixEdgePathH
public import proofs.PhosphorylationStableCapacity.CoalescedPathLimitTransfer

@[expose] public section

namespace PhosphorylationStableCapacity

open Filter
open scoped Topology

noncomputable section

/-- The actual normalized first-prefix edge action on incidence-transpose
forcing columns. The inverse response is taken from the finite source
replacement system at parameter `r`. -/
def coalescedPrefixEdgeActionMatrix (m : ℕ) (r : ℝ) :
    Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ :=
  fun i j => coalescedNormalizedEdgeAction m r
    (coalescedPrefixEdgeForcing m j) i

/-- Every entry of the normalized finite edge-action matrix converges to
the source's explicit Hurwitz path block. -/
theorem coalescedPrefixEdgeActionMatrix_tendsto (m : ℕ)
    (i j : Fin (m + 1)) :
    Tendsto (fun r : ℝ => coalescedPrefixEdgeActionMatrix m r i j)
      atTop (𝓝 (coalescedPathBlock m i j)) := by
  have h := coalescedNormalizedEdgeAction_tendsto m
    (coalescedPrefixEdgeForcing m j)
    (coalescedPrefixEdgeForcing_sum m j)
    (coalescedPrefixEdgeForcing_last m j) i
  have hpath := coalescedPrefixEdgeForcing_pathH m i j
  simp only [Fin.val_castSucc] at hpath
  rw [hpath, coalescedPrefixEdgeForcing_feedback] at h
  simpa only [coalescedPrefixEdgeActionMatrix,
    coalescedPathBlock] using h

/-- The normalized first-prefix edge-action matrix is eventually Hurwitz.
This is a matrix-level result; identifying it with the slow spectrum of the
literal class Jacobian requires a separate spectral transfer. -/
theorem coalescedPrefixEdgeActionMatrix_eventually_hurwitz (m : ℕ) :
    ∀ᶠ r : ℝ in atTop, IsHurwitz (coalescedPrefixEdgeActionMatrix m r) := by
  exact coalescedPathBlock_eventually_hurwitz_of_entrywise_limit m
    (coalescedPrefixEdgeActionMatrix m)
    (coalescedPrefixEdgeActionMatrix_tendsto m)

end
end PhosphorylationStableCapacity
