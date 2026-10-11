module
public import proofs.PhosphorylationStableCapacity.SourceCurrentResponseChain
public import proofs.PhosphorylationStableCapacity.SourceAugmentedRankOne

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section
open PhosphorylationSharpness

/-- At every positive literal equilibrium, the negative restricted
Jacobian and the physical augmented total/current matrix have the
same parity-adjusted determinant sign. -/
theorem equilibrium_restricted_jacobian_parity_det_pos_iff_augmented
    {n : ℕ} (k : Rates n) (x : State n)
    (hk : k.Positive) (hx : x.Positive)
    (heq : Equilibrium k x) :
    0 < (-1 : ℝ)^n *
      (restrictedJacobianMatrix (totalE x) (totalF x) (totalS x)
        k (toCoordinateSpace (chart x))).det ↔
    0 < (-1 : ℝ)^n *
      (sourceAugmentedCurrentMatrix k x).det := by
  let u := loadedCoordOfState x
  have hback : stateFromLoaded (totalE x) (totalF x) (totalS x) u = x :=
    stateFromLoaded_loadedCoordOfState _ _ _ x ⟨rfl, rfl, rfl⟩
  have hcoord : fromLoadedCoord u = toCoordinateSpace (chart x) := by
    simp [u, loadedCoordOfState, from_toLoadedCoord]
  have hschur := source_jacobian_parity_det_sign_iff_schur
    (totalE x) (totalF x) (totalS x) k u hk
    (by rw [hback]; exact hx) (by rw [hback]; exact heq)
  rw [hcoord, sourceSlowSchurMatrix_det_eq_current_response_det] at hschur
  have haug := equilibrium_sourceCurrentResponse_augmented_parity_iff
    k x hk hx heq
  exact hschur.trans haug

/-- The entire determinant orientation question reduces to an explicit
two-moment expression in the positive literal state. -/
theorem equilibrium_restricted_jacobian_parity_det_pos_iff_moment
    {n : ℕ} (k : Rates n) (x : State n)
    (hk : k.Positive) (hx : x.Positive)
    (heq : Equilibrium k x) :
    0 < (-1 : ℝ)^n *
      (restrictedJacobianMatrix (totalE x) (totalF x) (totalS x)
        k (toCoordinateSpace (chart x))).det ↔
    0 < (1 - sourcePathFirstMoment (sourceOccupancyDifference x)) *
        sourcePathZerothMoment (sourceAugmentedTotalRow x) +
      sourcePathZerothMoment (sourceOccupancyDifference x) *
        sourcePathFirstMoment (sourceAugmentedTotalRow x) := by
  rw [equilibrium_restricted_jacobian_parity_det_pos_iff_augmented
    k x hk hx heq]
  exact sourceAugmentedCurrentMatrix_parity_det_pos_iff_moment
    k x hk hx

end
end PhosphorylationStableCapacity
