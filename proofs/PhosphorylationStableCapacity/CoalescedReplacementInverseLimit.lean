module
public import Mathlib.Topology.Instances.Matrix
public import proofs.PhosphorylationStableCapacity.CoalescedReplacementNonsingular
public import proofs.PhosphorylationStableCapacity.CoalescedReplacementEquation

@[expose] public section

namespace PhosphorylationStableCapacity

open Filter
open scoped Topology

noncomputable section

/-- Entrywise convergence of the literal replacement matrix is convergence
in its finite-dimensional matrix topology. -/
theorem coalescedReplacementMass_tendsto_matrix (m : ℕ) :
    Tendsto (coalescedReplacementMass m) atTop
      (𝓝 (coalescedReplacementLimit m)) := by
  apply tendsto_pi_nhds.mpr
  intro i
  apply tendsto_pi_nhds.mpr
  intro j
  exact coalescedReplacementMass_tendsto m i j

/-- Its inverse converges to the inverse of the nonsingular literal limit. -/
theorem coalescedReplacementMass_inv_tendsto (m : ℕ) :
    Tendsto (fun r : ℝ => (coalescedReplacementMass m r)⁻¹)
      atTop (𝓝 ((coalescedReplacementLimit m)⁻¹)) := by
  have hdet := coalescedReplacementLimit_det_ne_zero m
  have hcont : ContinuousAt (Inv.inv :
      Matrix (Fin (m + 3)) (Fin (m + 3)) ℝ →
        Matrix (Fin (m + 3)) (Fin (m + 3)) ℝ)
      (coalescedReplacementLimit m) :=
    continuousAt_matrix_inv _ (by simpa using continuousAt_inv₀ hdet)
  exact hcont.tendsto.comp (coalescedReplacementMass_tendsto_matrix m)

/-- Every literal zero-sum edge response converges to the solution of the
source-specific limiting replacement system. -/
theorem coalescedInverseResponse_tendsto_replacement_solution
    (m : ℕ) (q : Fin (m + 3) → ℝ)
    (hqsum : (∑ i : Fin (m + 3), q i) = 0)
    (hqlast : q (Fin.last (m + 2)) = 0) :
    Tendsto (fun r : ℝ => coalescedInverseResponse m r q) atTop
      (𝓝 ((coalescedReplacementLimit m)⁻¹.mulVec
        (coalescedReplacementTarget m q))) := by
  have hdetlim : Tendsto (fun r : ℝ =>
      (coalescedReplacementMass m r).det) atTop
      (𝓝 (coalescedReplacementLimit m).det) :=
    (continuous_id.matrix_det.continuousAt.tendsto).comp
      (coalescedReplacementMass_tendsto_matrix m)
  have hdet : ∀ᶠ r : ℝ in atTop,
      (coalescedReplacementMass m r).det ≠ 0 :=
    hdetlim.eventually (eventually_ne_nhds
      (coalescedReplacementLimit_det_ne_zero m))
  have heq := coalescedInverseResponse_eventually_replacement_equation
    m q hqsum hqlast
  have hlim : Tendsto (fun r : ℝ =>
      (coalescedReplacementMass m r)⁻¹.mulVec
        (coalescedReplacementTarget m q)) atTop
      (𝓝 ((coalescedReplacementLimit m)⁻¹.mulVec
        (coalescedReplacementTarget m q))) := by
    have hcont : Continuous (fun A :
        Matrix (Fin (m + 3)) (Fin (m + 3)) ℝ =>
          A.mulVec (coalescedReplacementTarget m q)) :=
      continuous_id.matrix_mulVec continuous_const
    exact hcont.continuousAt.tendsto.comp
      (coalescedReplacementMass_inv_tendsto m)
  apply hlim.congr'
  filter_upwards [hdet, heq] with r hdet heq
  have hunit : IsUnit (coalescedReplacementMass m r).det :=
    isUnit_iff_ne_zero.mpr hdet
  have hsolve : coalescedInverseResponse m r q =
      (coalescedReplacementMass m r)⁻¹.mulVec
        (coalescedReplacementTarget m q) := by
    rw [← heq, Matrix.mulVec_mulVec,
      Matrix.nonsing_inv_mul _ hunit, Matrix.one_mulVec]
  exact hsolve.symm

end
end PhosphorylationStableCapacity
