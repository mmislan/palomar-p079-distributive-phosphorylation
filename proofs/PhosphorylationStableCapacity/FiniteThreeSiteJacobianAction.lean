module
public import proofs.PhosphorylationStableCapacity.FiniteThreeSiteJacobianInterior

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section
open PhosphorylationSharpness Module

theorem threeSiteField_hasFDerivAt (ET FT ST : ℝ) (k : Rates 3)
    (u : CoordinateSpace 3) :
    HasFDerivAt (threeSiteField ET FT ST k)
      (threeSiteJacobianCLM ET FT ST k u) u := by
  have hs : HasFDerivAt
      (fun v : CoordinateSpace 3 => (threeSiteField ET FT ST k v).1)
      (ContinuousLinearMap.pi ![threeSiteRowS1 ET FT k u,
        threeSiteRowS2 ET FT k u, threeSiteRowS3 FT k u]) u := by
    apply hasFDerivAt_pi'.2
    intro i
    fin_cases i
    · simpa [threeSiteField, threeSiteRowS1] using
        threeSiteS1_hasFDerivAt ET FT k u
    · simpa [threeSiteField, threeSiteRowS2] using
        threeSiteS2_hasFDerivAt ET FT k u
    · simpa [threeSiteField] using threeSiteS3_hasFDerivAt FT k u
  have hc : HasFDerivAt
      (fun v : CoordinateSpace 3 => (threeSiteField ET FT ST k v).2.1)
      (ContinuousLinearMap.pi ![threeSiteRowC0 ET ST k u,
        threeSiteRowC1 ET k u, threeSiteRowC2 ET k u]) u := by
    apply hasFDerivAt_pi'.2
    intro i
    fin_cases i
    · simpa [threeSiteField] using threeSiteC0_hasFDerivAt ET ST k u
    · simpa [threeSiteField, threeSiteRowC1] using
        threeSiteCSucc_hasFDerivAt 0 ET k u
    · simpa [threeSiteField, threeSiteRowC2] using
        threeSiteCSucc_hasFDerivAt 1 ET k u
  have hd : HasFDerivAt
      (fun v : CoordinateSpace 3 => (threeSiteField ET FT ST k v).2.2)
      (ContinuousLinearMap.pi ![threeSiteRowD0 FT k u,
        threeSiteRowD1 FT k u, threeSiteRowD2 FT k u]) u := by
    apply hasFDerivAt_pi'.2
    intro i
    fin_cases i
    · simpa [threeSiteField, threeSiteRowD0] using
        threeSiteD_hasFDerivAt 0 FT k u
    · simpa [threeSiteField, threeSiteRowD1] using
        threeSiteD_hasFDerivAt 1 FT k u
    · simpa [threeSiteField, threeSiteRowD2] using
        threeSiteD_hasFDerivAt 2 FT k u
  simpa [threeSiteJacobianCLM] using hs.prodMk (hc.prodMk hd)

theorem restrictedJacobian_threeSite (ET FT ST : ℝ) (k : Rates 3)
    (u : CoordinateSpace 3) :
    restrictedJacobian ET FT ST k u = threeSiteJacobianCLM ET FT ST k u := by
  have hfield : restrictedFieldEuclid ET FT ST k = threeSiteField ET FT ST k :=
    funext (restrictedFieldEuclid_threeSite ET FT ST k)
  simp only [restrictedJacobian, hfield]
  exact (threeSiteField_hasFDerivAt ET FT ST k u).fderiv

end
end PhosphorylationStableCapacity
