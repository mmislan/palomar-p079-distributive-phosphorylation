module
public import proofs.PhosphorylationStableCapacity.CoalescedInverseModeIdentification

@[expose] public section

namespace PhosphorylationStableCapacity

open Filter
open scoped Topology

noncomputable section

/-- The actual finite scaled inverse response has the source's explicit
limiting form (5), with its constants satisfying (6) and feedback (7). -/
theorem coalescedInverseResponse_explicit_mode_limit (m : ℕ)
    (q : Fin (m + 3) → ℝ)
    (hqsum : (∑ j : Fin (m + 3), q j) = 0)
    (hqlast : q (Fin.last (m + 2)) = 0) :
    ∃ a b : ℝ,
      Tendsto (fun r : ℝ => coalescedInverseResponse m r q) atTop
        (𝓝 (coalescedInverseParticular m q +
          coalescedFullKernelVector m a b)) ∧
      (3 * coalescedInverseT m q / 2 + coalescedInverseU m q) +
        (7 - 3 * coalescedV m) * a / 2 +
          3 * coalescedV m * b / 2 = 0 ∧
      (4 - coalescedV m) * b =
        coalescedInverseT m q + (1 - coalescedV m) * a ∧
      2 * b - a =
        (10 * coalescedInverseT m q +
          (2 + coalescedV m) * coalescedInverseU m q) /
            (2 * (7 - 4 * coalescedV m)) := by
  let x := (coalescedReplacementLimit m)⁻¹.mulVec
    (coalescedReplacementTarget m q)
  have hunit : IsUnit (coalescedReplacementLimit m).det :=
    isUnit_iff_ne_zero.mpr (coalescedReplacementLimit_det_ne_zero m)
  have hsol : (coalescedReplacementLimit m).mulVec x =
      coalescedReplacementTarget m q := by
    dsimp [x]
    rw [Matrix.mulVec_mulVec,
      Matrix.mul_nonsing_inv _ hunit, Matrix.one_mulVec]
  obtain ⟨a, b, hrepr, hrow, hlast, hfeedback⟩ :=
    coalescedReplacementSolution_mode_identification
      m q x hqsum hqlast hsol
  have hlim := coalescedInverseResponse_tendsto_replacement_solution
    m q hqsum hqlast
  change Tendsto (fun r : ℝ => coalescedInverseResponse m r q)
    atTop (𝓝 x) at hlim
  rw [hrepr] at hlim
  exact ⟨a, b, hlim, hrow, hlast, hfeedback⟩

end
end PhosphorylationStableCapacity
