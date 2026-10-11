module
public import proofs.PhosphorylationStableCapacity.CoalescedKernelLastNonzero

@[expose] public section

namespace PhosphorylationStableCapacity

open Filter

noncomputable section

/-- The finite loaded slow-current zero mode can be normalized to have
final edge coordinate one. -/
theorem coalescedFullLoadedMatrix_eventually_normalized_kernel (m : ℕ) :
    ∀ᶠ r : ℝ in atTop,
      ∃ u : Fin (m + 2) → ℝ,
        u (Fin.last (m + 1)) = 1 ∧
          (coalescedFullLoadedMatrix m r).mulVec u = 0 := by
  filter_upwards [coalescedFullLoadedMatrix_eventually_kernel_last_ne_zero m]
    with r hkernel
  obtain ⟨z, hlast, hKz⟩ := hkernel
  let u : Fin (m + 2) → ℝ := (z (Fin.last (m + 1)))⁻¹ • z
  have hulast : u (Fin.last (m + 1)) = 1 := by
    simp [u, smul_eq_mul, hlast]
  have hKu : (coalescedFullLoadedMatrix m r).mulVec u = 0 := by
    dsimp [u]
    rw [Matrix.mulVec_smul, hKz, smul_zero]
  exact ⟨u, hulast, hKu⟩

end
end PhosphorylationStableCapacity
