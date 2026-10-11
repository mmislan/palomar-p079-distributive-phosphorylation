module
public import proofs.PhosphorylationStableCapacity.CoalescedAllEdgeKernel

@[expose] public section

namespace PhosphorylationStableCapacity

open Filter

noncomputable section

/-- The exact complete finite loaded slow-current matrix is singular for all
sufficiently large source parameters. This does not assert that its zero
eigenvalue is simple or that its complement is Hurwitz. -/
theorem coalescedFullLoadedMatrix_eventually_det_eq_zero (m : ℕ) :
    ∀ᶠ r : ℝ in atTop, (coalescedFullLoadedMatrix m r).det = 0 := by
  filter_upwards [coalescedFullLoadedMatrix_eventually_nontrivial_kernel m]
    with r hkernel
  obtain ⟨z, hz, hrows⟩ := hkernel
  let K := coalescedFullLoadedMatrix m r
  have hKz : K.mulVec z = 0 := by
    funext i
    exact hrows i
  by_contra hdet
  have hunit : IsUnit K.det := isUnit_iff_ne_zero.mpr hdet
  have hrecover : K⁻¹.mulVec (K.mulVec z) = z := by
    rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hunit,
      Matrix.one_mulVec]
  have hz0 : z = 0 := by
    calc
      z = K⁻¹.mulVec (K.mulVec z) := hrecover.symm
      _ = 0 := by rw [hKz]; simp
  exact hz hz0

end
end PhosphorylationStableCapacity
