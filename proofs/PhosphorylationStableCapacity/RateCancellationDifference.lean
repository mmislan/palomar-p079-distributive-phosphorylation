module
public import proofs.PhosphorylationStableCapacity.RateSelectedLinearEquiv

@[expose] public section

namespace PhosphorylationStableCapacity

open PhosphorylationSharpness

noncomputable section

/-- At each positive class point, displacement from a fixed selected
rate parameter is the explicit inverse response applied to the negative
field at those fixed rates. -/
theorem cancellationParameter_sub_eq_inverse_field {n : ℕ}
    (ET FT ST : ℝ) (k : Rates n) (u v : CoordinateSpace n)
    (hx : (stateFromLoaded ET FT ST u).Positive) :
    cancellationParameter ET FT ST k u - v =
      -selectedRateRightInverse (stateFromLoaded ET FT ST u)
        (loadedRestrictedField ET FT ST
          (ratesAdd k (selectedRates v)) u) := by
  let x := stateFromLoaded ET FT ST u
  let B := selectedRateRightInverseLinear x
  let fk := loadedRestrictedField ET FT ST k u
  let fv := loadedRestrictedField ET FT ST (selectedRates v) u
  have hleft : B fv = v :=
    selectedRateRightInverse_response ET FT ST u v hx
  change B (-fk) - v =
    -B (loadedRestrictedField ET FT ST
      (ratesAdd k (selectedRates v)) u)
  rw [loadedRestrictedField_ratesAdd]
  change B (-fk) - v = -B (fk + fv)
  rw [map_neg, map_add, hleft]
  abel

end
end PhosphorylationStableCapacity
