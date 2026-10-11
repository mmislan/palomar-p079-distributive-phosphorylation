module
public import proofs.PhosphorylationStableCapacity.RateVariationSurjective

@[expose] public section

namespace PhosphorylationStableCapacity

open PhosphorylationSharpness Matrix

noncomputable section

/-- The response in loaded class coordinates to independently prescribed
current and two complex velocities. -/
def rateVariationResponse (n : ℕ) :
    CoordinateSpace n →ₗ[ℝ] CoordinateSpace n where
  toFun v := ((projectedPathIncidence n).mulVec v.1, v.2)
  map_add' v w := by
    ext i <;> simp [Matrix.mulVec_add]
  map_smul' t v := by
    ext i <;> simp [Matrix.mulVec_smul]

theorem rateVariationResponse_surjective (n : ℕ) :
    Function.Surjective (rateVariationResponse n) := by
  intro y
  obtain ⟨r, hr⟩ :=
    (Matrix.mulVec_surjective_iff_isUnit.mpr
      (projectedPathIncidence_isUnit n)) y.1
  refine ⟨⟨r, y.2⟩, ?_⟩
  simp [rateVariationResponse, hr]

/-- A three-list family of literal rate perturbations. The base state is
fixed, so these perturbations may have either sign. -/
def rateVariationParameterField {n : ℕ} (ET FT ST : ℝ)
    (u : CoordinateSpace n) (v : CoordinateSpace n) : CoordinateSpace n :=
  let x := stateFromLoaded ET FT ST u
  loadedRestrictedField ET FT ST
    (rateVariation x v.2.1 v.2.2 v.1) u

theorem rateVariationParameterField_eq_response {n : ℕ}
    (ET FT ST : ℝ) (u : CoordinateSpace n)
    (hx : (stateFromLoaded ET FT ST u).Positive)
    (v : CoordinateSpace n) :
    rateVariationParameterField ET FT ST u v =
      rateVariationResponse n v := by
  apply Prod.ext
  · rw [rateVariationParameterField,
      loadedRestrictedField_slow_eq_incidence]
    rw [show catalyticCurrent
        (rateVariation (stateFromLoaded ET FT ST u) v.2.1 v.2.2 v.1)
        (stateFromLoaded ET FT ST u) = v.1 from by
          funext i
          exact rateVariation_current _ hx _ _ _ i]
    rfl
  · apply Prod.ext
    · funext i
      simpa [rateVariationParameterField, rateVariationResponse,
        loadedRestrictedField, restrictedFieldEuclid,
        restrictedField, chart, toLoadedCoord, toCoordinateSpace,
        stateFromLoaded] using
        rateVariation_C (stateFromLoaded ET FT ST u) hx
          v.2.1 v.2.2 v.1 i
    · funext i
      simpa [rateVariationParameterField, rateVariationResponse,
        loadedRestrictedField, restrictedFieldEuclid,
        restrictedField, chart, toLoadedCoord, toCoordinateSpace,
        stateFromLoaded] using
        rateVariation_D (stateFromLoaded ET FT ST u) hx
          v.2.1 v.2.2 v.1 i

/-- The actual Fréchet derivative of this literal rate-variation family is
onto the exact loaded class velocity space. -/
theorem rateVariationParameterField_fderiv_surjective {n : ℕ}
    (ET FT ST : ℝ) (u v : CoordinateSpace n)
    (hx : (stateFromLoaded ET FT ST u).Positive) :
    Function.Surjective
      (fderiv ℝ (rateVariationParameterField ET FT ST u) v) := by
  have hfun : rateVariationParameterField ET FT ST u =
      rateVariationResponse n := by
    funext w
    exact rateVariationParameterField_eq_response ET FT ST u hx w
  rw [hfun]
  change Function.Surjective
    (fderiv ℝ (rateVariationResponse n).toContinuousLinearMap v)
  rw [ContinuousLinearMap.fderiv]
  simpa using rateVariationResponse_surjective n

end
end PhosphorylationStableCapacity
