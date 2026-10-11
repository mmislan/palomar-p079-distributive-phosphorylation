module
public import proofs.PhosphorylationStableCapacity.SourceMomentSlopeAlgebra
public import proofs.PhosphorylationStableCapacity.SourceCurrentResponseChain
public import proofs.PhosphorylationStableCapacity.SourceAugmentedRankOne

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section

open PhosphorylationSharpness Matrix

/-- Exact elimination of the affine current-kernel equation against the
substrate-total tangent. This upgrades the sign step used in the split
chart to a magnitude identity. -/
theorem affine_current_moment_magnitude
    (T0 T1 Q0 Q1 a b H : ℝ)
    (hcurrent : a*Q0+b*(Q1-1)=0)
    (htotal : H=a*T0+b*T1) :
    b*((1-Q1)*T0+Q0*T1)=Q0*H := by
  linear_combination -T0*hcurrent - Q0*htotal

/-- Exact magnitude chain behind the manuscript's Jacobian determinant
formula. It retains every coordinate-change and fast-block determinant,
which the prior orientation theorem intentionally discarded. -/
theorem equilibrium_restricted_jacobian_det_magnitude_chain
    {n : ℕ} (k : Rates n) (x : State n)
    (hk : k.Positive) (hx : x.Positive)
    (heq : Equilibrium k x) :
    let u := loadedCoordOfState x
    let D := LinearMap.toMatrix (fastBasis n) (fastBasis n)
      (loadedBlockD (totalE x) (totalF x) (totalS x) k u).toLinearMap
    let M := sourceConstrainedBindingMass x
    let pivot := sourceAugmentedCurrentMatrix k x 0 0
    (restrictedJacobianMatrix (totalE x) (totalF x) (totalS x)
      k (toCoordinateSpace (chart x))).det * M.det * pivot =
      D.det *
        (∏ i : Fin (n+1), sourceAugmentedRowWeight k x i) *
          ((-1 : ℝ)^n *
            ((1 - sourcePathFirstMoment (sourceOccupancyDifference x)) *
                sourcePathZerothMoment (sourceAugmentedTotalRow x) +
              sourcePathZerothMoment (sourceOccupancyDifference x) *
                sourcePathFirstMoment (sourceAugmentedTotalRow x))) := by
  dsimp only
  let u := loadedCoordOfState x
  let D := LinearMap.toMatrix (fastBasis n) (fastBasis n)
    (loadedBlockD (totalE x) (totalF x) (totalS x) k u).toLinearMap
  let M := sourceConstrainedBindingMass x
  let R := sourceCurrentResponseMatrix (totalE x) (totalF x)
    (totalS x) k u
  let A := sourceAugmentedCurrentMatrix k x
  let pivot := A 0 0
  have hback : stateFromLoaded (totalE x) (totalF x) (totalS x) u = x :=
    stateFromLoaded_loadedCoordOfState _ _ _ x ⟨rfl, rfl, rfl⟩
  have hcoord : fromLoadedCoord u = toCoordinateSpace (chart x) := by
    simp [u, loadedCoordOfState, from_toLoadedCoord]
  obtain ⟨_, hschur⟩ := source_jacobian_det_eq_positive_fast_mul_schur
    (totalE x) (totalF x) (totalS x) k u hk
    (by rw [hback]; exact hx) (by rw [hback]; exact heq)
  change (restrictedJacobianMatrix (totalE x) (totalF x) (totalS x)
      k (fromLoadedCoord u)).det =
    D.det * (sourceSlowSchurMatrix (totalE x) (totalF x)
      (totalS x) k u).det at hschur
  rw [hcoord, sourceSlowSchurMatrix_det_eq_current_response_det] at hschur
  have hJ :
      (restrictedJacobianMatrix (totalE x) (totalF x) (totalS x)
        k (toCoordinateSpace (chart x))).det = D.det * R.det := by
    simpa only [D, R, sourceSlowSchurMatrix] using hschur
  have hR : R.det * M.det = (sourceConstrainedCurrentDerivative k x).det := by
    rw [← Matrix.det_mul]
    exact congrArg Matrix.det
      (equilibrium_sourceCurrentResponse_mul_constrainedMass k x hk hx heq)
  have hA : A.det = pivot * (sourceConstrainedCurrentDerivative k x).det :=
    sourceAugmentedCurrentMatrix_det_eq_pivot_mul_constrained k x hx
  have hmoment := sourceAugmentedCurrentMatrix_det_rank_one k x
    (ne_of_gt (sourceAugmentedTotalRow_zeroth_pos x hx))
  calc
    (restrictedJacobianMatrix (totalE x) (totalF x) (totalS x)
      k (toCoordinateSpace (chart x))).det * M.det * pivot =
        D.det * (R.det * M.det) * pivot := by rw [hJ]; ring
    _ = D.det * (sourceConstrainedCurrentDerivative k x).det * pivot := by
          rw [hR]
    _ = D.det * A.det := by rw [hA]; ring
    _ = D.det *
        (∏ i : Fin (n+1), sourceAugmentedRowWeight k x i) *
          ((-1 : ℝ)^n *
            ((1 - sourcePathFirstMoment (sourceOccupancyDifference x)) *
                sourcePathZerothMoment (sourceAugmentedTotalRow x) +
              sourcePathZerothMoment (sourceOccupancyDifference x) *
                sourcePathFirstMoment (sourceAugmentedTotalRow x))) := by
          rw [hmoment]
          ring

end
end PhosphorylationStableCapacity
