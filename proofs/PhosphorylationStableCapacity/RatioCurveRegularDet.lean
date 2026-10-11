module
public import proofs.PhosphorylationStableCapacity.RatioCurveRegularRoot
public import Mathlib.LinearAlgebra.Determinant

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section
open PhosphorylationSharpness

/-- The literal nonzero restricted matrix determinant gives an
injective class Jacobian. -/
theorem restrictedJacobian_injective_of_det_ne_zero {n : ℕ}
    (ET FT ST : ℝ) (k : Rates n) (z : CoordinateSpace n)
    (hdet : (restrictedJacobianMatrix ET FT ST k z).det ≠ 0) :
    Function.Injective (restrictedJacobian ET FT ST k z) := by
  let L := (restrictedJacobian ET FT ST k z).toLinearMap
  have hdetL : LinearMap.det L ≠ 0 := by
    rw [← LinearMap.det_toMatrix (coordinateBasis n) L]
    exact hdet
  have hunitDet : IsUnit (LinearMap.det L) :=
    isUnit_iff_ne_zero.mpr hdetL
  have hunitL : IsUnit L :=
    (LinearMap.isUnit_iff_isUnit_det L).2 hunitDet
  have hker : LinearMap.ker L = ⊥ :=
    (LinearMap.isUnit_iff_ker_eq_bot L).1 hunitL
  have hinj : Function.Injective L := by
    rwa [LinearMap.ker_eq_bot] at hker
  exact hinj

/-- Every regular positive literal equilibrium in the scalar chart
corresponds to a simple residual root. -/
theorem ratio_residual_deriv_ne_zero_of_regular_jacobian {n : ℕ}
    (hn : 0 < n) (k : Rates n) (hk : k.Positive)
    (ET FT ST u : ℝ) (hFT : 0 < FT) (hST : 0 < ST)
    (hu : 0 < u)
    (hroot : ratioEnzymeResidual k ET FT ST u = 0)
    (hdet : (restrictedJacobianMatrix ET FT ST k
      (ratioEquilibriumCurveChart k FT ST u)).det ≠ 0) :
    deriv (ratioEnzymeResidual k ET FT ST) u ≠ 0 :=
  ratio_residual_deriv_ne_zero_of_restrictedJacobian_injective
    hn k hk ET FT ST u hFT hST hu hroot
    (restrictedJacobian_injective_of_det_ne_zero ET FT ST k
      (ratioEquilibriumCurveChart k FT ST u) hdet)

end
end PhosphorylationStableCapacity
