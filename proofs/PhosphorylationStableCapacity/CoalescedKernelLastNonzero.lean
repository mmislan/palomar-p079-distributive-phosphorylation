module
public import proofs.PhosphorylationStableCapacity.CoalescedAllEdgeKernel
public import proofs.PhosphorylationStableCapacity.PrefixKernelLast

@[expose] public section

namespace PhosphorylationStableCapacity

open Filter

noncomputable section

/-- At sufficiently large finite source parameters, the complete slow
matrix has a kernel vector whose final edge coordinate is nonzero. -/
theorem coalescedFullLoadedMatrix_eventually_kernel_last_ne_zero (m : ℕ) :
    ∀ᶠ r : ℝ in atTop,
      ∃ z : Fin (m + 2) → ℝ,
        z (Fin.last (m + 1)) ≠ 0 ∧
          (coalescedFullLoadedMatrix m r).mulVec z = 0 := by
  filter_upwards [coalescedFullLoadedMatrix_eventually_nontrivial_kernel m,
    coalescedFullLoadedMatrix_prefix_eventually_hurwitz m]
    with r hkernel hprefix
  obtain ⟨z, hz, hrows⟩ := hkernel
  have hKz : (coalescedFullLoadedMatrix m r).mulVec z = 0 := by
    funext i
    exact hrows i
  have hdet : Matrix.det (fun i j : Fin (m + 1) =>
      coalescedFullLoadedMatrix m r i.castSucc j.castSucc) ≠ 0 :=
    isHurwitz_det_ne_zero hprefix
  have hlast := kernel_last_ne_zero_of_prefix_det_ne_zero (m + 1)
    (coalescedFullLoadedMatrix m r) hdet z hz hKz
  exact ⟨z, hlast, hKz⟩

end
end PhosphorylationStableCapacity
