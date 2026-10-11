module
public import proofs.PhosphorylationStableCapacity.LoadedJacobianBlockMatrix
public import proofs.PhosphorylationStableCapacity.LoadedJacobianConjugacy
public import Mathlib.LinearAlgebra.Charpoly.ToMatrix

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section

open PhosphorylationSharpness

/-- The loaded and original class-restricted Jacobian matrices have the
same characteristic polynomial at corresponding points of the affine
chart. -/
theorem loadedJacobianMatrix_charpoly_eq_restricted {n : ℕ}
    (ET FT ST : ℝ) (k : Rates n) (u : CoordinateSpace n) :
    (loadedJacobianMatrix ET FT ST k u).charpoly =
      (restrictedJacobianMatrix ET FT ST k (fromLoadedCoord u)).charpoly := by
  have hlin :
      (fderiv ℝ (loadedRestrictedField ET FT ST k) u).toLinearMap =
        (loadedCoordLinear n).conj
          (restrictedJacobian ET FT ST k (fromLoadedCoord u)).toLinearMap := by
    apply LinearMap.ext
    intro v
    simp [loadedRestrictedFderiv_conjugate, LinearEquiv.conj_apply,
      loadedCoordContinuous_apply, loadedCoordContinuous_symm_apply,
      loadedCoordLinear_apply, loadedCoordLinear_symm_apply]
  rw [loadedJacobianMatrix, restrictedJacobianMatrix, hlin,
    LinearMap.charpoly_toMatrix, LinearMap.charpoly_toMatrix,
    LinearEquiv.charpoly_conj]

end
end PhosphorylationStableCapacity
