module
public import Mathlib.Analysis.Normed.Operator.Banach
public import proofs.PhosphorylationStableCapacity.LoadedChartLinear
public import Mathlib.Analysis.Calculus.FDeriv.Equiv
public import Mathlib.Analysis.Normed.Module.FiniteDimension

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section
open PhosphorylationSharpness

/-- The loaded change of coordinates as a continuous linear equivalence. -/
def loadedCoordContinuous (n : ℕ) :
    CoordinateSpace n ≃L[ℝ] CoordinateSpace n :=
  (loadedCoordLinear n).toContinuousLinearEquivOfContinuous
    (LinearMap.continuous_of_finiteDimensional
      (loadedCoordLinear n).toLinearMap)

@[simp] theorem loadedCoordContinuous_apply {n : ℕ} (u : CoordinateSpace n) :
    loadedCoordContinuous n u = toLoadedCoord u := rfl

@[simp] theorem loadedCoordContinuous_symm_apply {n : ℕ} (u : CoordinateSpace n) :
    (loadedCoordContinuous n).symm u = fromLoadedCoord u := by
  exact loadedCoordLinear_symm_apply u

theorem loadedRestrictedField_conjugate {n : ℕ} (ET FT ST : ℝ)
    (k : Rates n) :
    loadedRestrictedField ET FT ST k =
      (loadedCoordContinuous n) ∘
        (restrictedFieldEuclid ET FT ST k) ∘
          (loadedCoordContinuous n).symm := by
  funext u
  change toLoadedCoord (restrictedFieldEuclid ET FT ST k (fromLoadedCoord u)) =
    (loadedCoordContinuous n)
      (restrictedFieldEuclid ET FT ST k ((loadedCoordContinuous n).symm u))
  rw [loadedCoordContinuous_symm_apply, loadedCoordContinuous_apply]

/-- The actual class-restricted derivative conjugated into loaded coordinates. -/
theorem loadedRestrictedFderiv_conjugate {n : ℕ} (ET FT ST : ℝ)
    (k : Rates n) (u : CoordinateSpace n) :
    fderiv ℝ (loadedRestrictedField ET FT ST k) u =
      (loadedCoordContinuous n : CoordinateSpace n →L[ℝ] CoordinateSpace n).comp
        ((restrictedJacobian ET FT ST k
          ((loadedCoordContinuous n).symm u)).comp
          ((loadedCoordContinuous n).symm :
            CoordinateSpace n →L[ℝ] CoordinateSpace n)) := by
  rw [loadedRestrictedField_conjugate]
  rw [ContinuousLinearEquiv.comp_fderiv]
  congr 1
  rw [ContinuousLinearEquiv.comp_right_fderiv]
  rfl

end
end PhosphorylationStableCapacity
