module
public import proofs.PhosphorylationStableCapacity.CoalescedPrefixLoadedHurwitz

@[expose] public section

namespace PhosphorylationStableCapacity

open Filter

noncomputable section

/-- Every incidence-transpose edge column of the substrate path, including
the final edge. -/
def coalescedFullEdgeForcingMatrix (m : ℕ) :
    Matrix (Fin (m + 3)) (Fin (m + 2)) ℝ :=
  fun k j => (if k = j.succ then 1 else 0) -
    (if k = j.castSucc then 1 else 0)

/-- The exact all-edge loaded slow-current matrix at the coalesced source.
Its first-prefix principal block is strictly Hurwitz for large parameters;
the final edge and zero eigenvalue still require spectral analysis. -/
def coalescedFullLoadedMatrix (m : ℕ) (r : ℝ) :
    Matrix (Fin (m + 2)) (Fin (m + 2)) ℝ :=
  coalescedCurrentJacobianMatrix m r *
    (coalescedFullMass m r)⁻¹ * coalescedFullEdgeForcingMatrix m

theorem coalescedFullEdgeForcing_prefix (m : ℕ)
    (k : Fin (m + 3)) (j : Fin (m + 1)) :
    coalescedFullEdgeForcingMatrix m k j.castSucc =
      coalescedPrefixForcingMatrix m k j := by
  unfold coalescedFullEdgeForcingMatrix
    coalescedPrefixForcingMatrix coalescedPrefixEdgeForcing
  have hindex : (j.castSucc.succ : Fin (m + 3)) =
      j.succ.castSucc := by
    ext
    rfl
  rw [hindex]

/-- The proved stable prefix is literally the leading principal block of
the all-edge slow-current matrix, with no limiting or reduced-model shortcut. -/
theorem coalescedFullLoadedMatrix_prefix (m : ℕ) (r : ℝ)
    (i j : Fin (m + 1)) :
    coalescedFullLoadedMatrix m r i.castSucc j.castSucc =
      coalescedPrefixLoadedMatrix m r i j := by
  classical
  unfold coalescedFullLoadedMatrix coalescedPrefixLoadedMatrix
  simp only [Matrix.mul_apply]
  congr 1

theorem coalescedFullLoadedMatrix_prefix_eventually_hurwitz (m : ℕ) :
    ∀ᶠ r : ℝ in atTop,
      IsHurwitz (fun i j : Fin (m + 1) =>
        coalescedFullLoadedMatrix m r i.castSucc j.castSucc) := by
  filter_upwards [coalescedPrefixLoadedMatrix_eventually_hurwitz m]
    with r hr
  simpa only [coalescedFullLoadedMatrix_prefix] using hr

end
end PhosphorylationStableCapacity
