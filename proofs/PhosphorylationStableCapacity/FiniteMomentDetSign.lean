module
public import proofs.PhosphorylationStableCapacity.ExactJacobianScalarMagnitude
public import proofs.PhosphorylationStableCapacity.SplitDeterminantSlowSign
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Linarith

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section
open PhosphorylationSharpness Matrix

/-- The all-size literal determinant orientation also has a negative-sign
version. This lets an exact scalar moment certificate replace a large
determinant computation at a fixed saddle. -/
theorem equilibrium_restricted_jacobian_parity_det_neg_iff_moment
    {n : ℕ} (k : Rates n) (x : State n)
    (hk : k.Positive) (hx : x.Positive)
    (heq : Equilibrium k x) :
    (-1 : ℝ)^n *
      (restrictedJacobianMatrix (totalE x) (totalF x) (totalS x)
        k (toCoordinateSpace (chart x))).det < 0 ↔
      (1 - sourcePathFirstMoment (sourceOccupancyDifference x)) *
        sourcePathZerothMoment (sourceAugmentedTotalRow x) +
      sourcePathZerothMoment (sourceOccupancyDifference x) *
        sourcePathFirstMoment (sourceAugmentedTotalRow x) < 0 := by
  let J := restrictedJacobianMatrix (totalE x) (totalF x) (totalS x)
    k (toCoordinateSpace (chart x))
  let D := LinearMap.toMatrix (fastBasis n) (fastBasis n)
    (loadedBlockD (totalE x) (totalF x) (totalS x) k
      (loadedCoordOfState x)).toLinearMap
  let M := sourceConstrainedBindingMass x
  let pivot := sourceAugmentedCurrentMatrix k x 0 0
  let W := ∏ i : Fin (n+1), sourceAugmentedRowWeight k x i
  let P : ℝ := (-1)^n
  let B :=
    (1 - sourcePathFirstMoment (sourceOccupancyDifference x)) *
      sourcePathZerothMoment (sourceAugmentedTotalRow x) +
    sourcePathZerothMoment (sourceOccupancyDifference x) *
      sourcePathFirstMoment (sourceAugmentedTotalRow x)
  have hstate : stateFromLoaded (totalE x) (totalF x) (totalS x)
      (loadedCoordOfState x) = x :=
    stateFromLoaded_loadedCoordOfState _ _ _ x ⟨rfl, rfl, rfl⟩
  have hDpos : 0 < D.det := by
    dsimp only [D]
    exact loaded_source_fast_block_det_pos
      (totalE x) (totalF x) (totalS x) k
      (loadedCoordOfState x) hk
      (by rw [hstate]; exact hx)
      (by rw [hstate]; exact heq)
  have hMpos : 0 < M.det := sourceConstrainedBindingMass_det_pos x hx
  have hpivot : 0 < pivot := sourceAugmentedCurrentMatrix_pivot_pos k x hx
  have hWpos : 0 < W := sourceAugmentedRowWeight_prod_pos k x hk hx
  have hmag : J.det * M.det * pivot = D.det * W * (P * B) := by
    simpa only [J, D, M, pivot, W, P, B] using
      (equilibrium_restricted_jacobian_det_magnitude_chain k x hk hx heq)
  have hparity : P * P = 1 := by
    dsimp only [P]
    rw [← pow_add, show n + n = 2*n by omega, pow_mul]
    norm_num
  have hmag2 : (P * J.det) * (M.det * pivot) = (D.det * W) * B := by
    calc
      (P * J.det) * (M.det * pivot) =
          P * (J.det * M.det * pivot) := by ring
      _ = P * (D.det * W * (P * B)) := by rw [hmag]
      _ = (P * P) * (D.det * W * B) := by ring
      _ = (D.det * W) * B := by rw [hparity]; ring
  have hMP : 0 < M.det * pivot := mul_pos hMpos hpivot
  have hDW : 0 < D.det * W := mul_pos hDpos hWpos
  have hsign : P * J.det < 0 ↔ B < 0 := by
    constructor
    · intro h
      have hleft : 0 < (-(P * J.det)) * (M.det * pivot) :=
        mul_pos (neg_pos.mpr h) hMP
      have hright : 0 < (D.det * W) * (-B) := by
        nlinarith [hmag2]
      exact neg_pos.mp ((mul_pos_iff_of_pos_left hDW).mp hright)
    · intro h
      have hright : 0 < (D.det * W) * (-B) :=
        mul_pos hDW (neg_pos.mpr h)
      have hleft : 0 < (-(P * J.det)) * (M.det * pivot) := by
        nlinarith [hmag2]
      exact neg_pos.mp ((mul_pos_iff_of_pos_right hMP).mp hleft)
  simpa only [J, P, B] using hsign

end
end PhosphorylationStableCapacity
