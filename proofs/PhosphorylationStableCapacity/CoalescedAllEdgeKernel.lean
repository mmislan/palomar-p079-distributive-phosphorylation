module
public import proofs.PhosphorylationStableCapacity.CoalescedAffineMassTotalZero
public import proofs.PhosphorylationStableCapacity.CoalescedFullLoadedMatrix
public import proofs.PhosphorylationStableCapacity.CoalescedFullMassPositive
public import proofs.PhosphorylationStableCapacity.PathIncidenceSurjectivity

@[expose] public section

namespace PhosphorylationStableCapacity

open Filter

noncomputable section

/-- The all-edge forcing matrix is exactly the transpose incidence of the
full substrate path, including its final edge. -/
theorem coalescedFullEdgeForcing_eq_incidence (m : ℕ) :
    coalescedFullEdgeForcingMatrix m =
      (pathIncidence (m + 2)).transpose := by
  ext k j
  rfl

/-- The complete finite loaded slow-current matrix has a nonzero kernel
vector for every sufficiently large source parameter. This is exact
singularity, not yet algebraic simplicity or full class-Jacobian stability. -/
theorem coalescedFullLoadedMatrix_eventually_nontrivial_kernel (m : ℕ) :
    ∀ᶠ r : ℝ in atTop,
      ∃ z : Fin (m + 2) → ℝ,
        z ≠ 0 ∧
          ∀ i : Fin (m + 2),
            (coalescedFullLoadedMatrix m r).mulVec z i = 0 := by
  filter_upwards [coalescedAffineZeroTangent_eventually_current_zero m,
    coalescedAffineZeroTangent_eventually_mass_total_zero m,
    coalescedFullMass_eventually_det_ne_zero m,
    eventually_gt_atTop (1 : ℝ)] with r hcurrent htotal hdet hr
  let σ := coalescedAffineZeroTangent m r
  let q := (coalescedFullMass m r).mulVec σ
  have hqsum : (∑ k : Fin (m + 3), q k) = 0 := by
    simpa only [q, σ] using htotal
  obtain ⟨z, hz⟩ := pathIncidence_transpose_zero_sum_range
    (m := m + 2) (by omega) q hqsum
  have hQ : (coalescedFullEdgeForcingMatrix m).mulVec z = q := by
    rw [coalescedFullEdgeForcing_eq_incidence]
    funext k
    exact hz k
  have hunit : IsUnit (coalescedFullMass m r).det :=
    isUnit_iff_ne_zero.mpr hdet
  have hrecover : (coalescedFullMass m r)⁻¹.mulVec q = σ := by
    dsimp [q]
    rw [Matrix.mulVec_mulVec,
      Matrix.nonsing_inv_mul _ hunit, Matrix.one_mulVec]
  have hznonzero : z ≠ 0 := by
    intro hz0
    have hq0 : q = 0 := by
      rw [← hQ, hz0]
      simp
    have hσ0 : σ = 0 := by
      calc
        σ = (coalescedFullMass m r)⁻¹.mulVec q := hrecover.symm
        _ = 0 := by rw [hq0]; simp
    exact (coalescedAffineZeroTangent_ne_zero m r hr) hσ0
  refine ⟨z, hznonzero, ?_⟩
  intro i
  change (coalescedCurrentJacobianMatrix m r *
    (coalescedFullMass m r)⁻¹ *
      coalescedFullEdgeForcingMatrix m).mulVec z i = 0
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    hQ, hrecover]
  exact hcurrent i

end
end PhosphorylationStableCapacity
