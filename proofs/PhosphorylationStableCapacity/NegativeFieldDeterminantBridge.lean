module
public import proofs.PhosphorylationStableCapacity.ClosedBallDegreeInterface
public import proofs.PhosphorylationStableCapacity.SignedNegativeFieldIndex

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section
open PhosphorylationSharpness

/-- The determinant in a generic regular-zero degree formula for the
negative literal field is exactly the determinant of the negative
ordered class Jacobian used in P079's signed-index definition. -/
theorem negative_restricted_field_derivative_det_eq {n : ℕ}
    (ET FT ST : ℝ) (k : Rates n) (u : CoordinateSpace n) :
    LinearMap.det
      (fderiv ℝ (fun y => -restrictedFieldEuclid ET FT ST k y) u).toLinearMap =
      (-(restrictedJacobianMatrix ET FT ST k u)).det := by
  rw [← LinearMap.det_toMatrix (coordinateBasis n)]
  simp [restrictedJacobianMatrix, restrictedJacobian]

theorem signedNegativeFieldIndex_eq_derivative_sign {n : ℕ}
    (ET FT ST : ℝ) (k : Rates n) (z : State n) :
    signedNegativeFieldIndex ET FT ST k z =
      (if 0 < LinearMap.det
        (fderiv ℝ (fun y => -restrictedFieldEuclid ET FT ST k y)
          (toCoordinateSpace (chart z))).toLinearMap
       then (1 : ℤ) else -1) := by
  rw [signedNegativeFieldIndex_eq_neg_matrix_det]
  rw [negative_restricted_field_derivative_det_eq]

end
end PhosphorylationStableCapacity
