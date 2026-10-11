module
public import proofs.PhosphorylationStableCapacity.RateSelectedParameter

@[expose] public section

namespace PhosphorylationStableCapacity

open PhosphorylationSharpness

noncomputable section

/-- Selected rate perturbations that cancel the class field at a specified
positive state. The formula is explicit, using the inverse path incidence. -/
def cancellationParameter {n : ℕ} (ET FT ST : ℝ)
    (k : Rates n) (u : CoordinateSpace n) : CoordinateSpace n :=
  selectedRateRightInverse (stateFromLoaded ET FT ST u)
    (-loadedRestrictedField ET FT ST k u)

/-- The selected-rate perturbation prescribed by `cancellationParameter`
makes the specified positive class state an exact literal equilibrium. -/
theorem loadedField_cancellationParameter_zero {n : ℕ}
    (ET FT ST : ℝ) (k : Rates n) (u : CoordinateSpace n)
    (hx : (stateFromLoaded ET FT ST u).Positive) :
    loadedRestrictedField ET FT ST
      (ratesAdd k (selectedRates (cancellationParameter ET FT ST k u))) u = 0 := by
  rw [loadedRestrictedField_ratesAdd]
  have h := selectedRates_response_right_inverse ET FT ST u
    (-loadedRestrictedField ET FT ST k u) hx
  simp [cancellationParameter, h]

end
end PhosphorylationStableCapacity
