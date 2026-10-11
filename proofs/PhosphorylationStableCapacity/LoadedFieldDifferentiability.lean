module
public import proofs.PhosphorylationStableCapacity.LoadedJacobianConjugacy

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section
open PhosphorylationSharpness

/-- The loaded compatibility-class vector field is differentiable because
it is a continuous linear conjugate of the polynomial restricted field. -/
theorem differentiable_loadedRestrictedField {n : ℕ} (ET FT ST : ℝ)
    (k : Rates n) : Differentiable ℝ (loadedRestrictedField ET FT ST k) := by
  rw [loadedRestrictedField_conjugate]
  exact (loadedCoordContinuous n).differentiable.comp
    ((differentiable_restrictedFieldEuclid ET FT ST k).comp
      (loadedCoordContinuous n).symm.differentiable)

end
end PhosphorylationStableCapacity
