module
public import proofs.PhosphorylationStableCapacity.FiniteThreeSiteJacobianAction

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section
open PhosphorylationSharpness

set_option maxHeartbeats 2000000

/-- Since the three-site class field is quadratic, its exact increment is its
Jacobian at the midpoint applied to the increment. -/
theorem threeSiteField_midpoint (ET FT ST : ℝ) (k : Rates 3)
    (u w : CoordinateSpace 3) :
    threeSiteField ET FT ST k (u + w) - threeSiteField ET FT ST k u =
      threeSiteJacobianCLM ET FT ST k (u + (1 / 2 : ℝ) • w) w := by
  ext i <;> fin_cases i <;>
    simp [threeSiteField, threeSiteJacobianCLM,
      threeSiteRowS1, threeSiteRowS2, threeSiteRowS3,
      threeSiteRowC0, threeSiteRowC1, threeSiteRowC2,
      threeSiteRowD0, threeSiteRowD1, threeSiteRowD2,
      threeSiteS0Linear, threeSiteELinear, threeSiteFLinear,
      threeSiteFreeS0, threeSiteFreeE, threeSiteFreeF] <;> ring

theorem restrictedFieldEuclid_midpoint_threeSite
    (ET FT ST : ℝ) (k : Rates 3) (u w : CoordinateSpace 3) :
    restrictedFieldEuclid ET FT ST k (u + w) -
      restrictedFieldEuclid ET FT ST k u =
        restrictedJacobian ET FT ST k (u + (1 / 2 : ℝ) • w) w := by
  rw [restrictedFieldEuclid_threeSite, restrictedFieldEuclid_threeSite,
    restrictedJacobian_threeSite]
  exact threeSiteField_midpoint ET FT ST k u w

end
end PhosphorylationStableCapacity
