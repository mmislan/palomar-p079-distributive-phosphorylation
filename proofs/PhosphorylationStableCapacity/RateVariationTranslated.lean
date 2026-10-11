module
public import proofs.PhosphorylationStableCapacity.RateVariationDerivative

@[expose] public section

namespace PhosphorylationStableCapacity

open PhosphorylationSharpness Matrix

noncomputable section

/-- Pointwise sum of two literal rate lists. -/
def ratesAdd {n : ℕ} (k l : Rates n) : Rates n where
  a i := k.a i + l.a i
  b i := k.b i + l.b i
  c i := k.c i + l.c i
  alpha i := k.alpha i + l.alpha i
  beta i := k.beta i + l.beta i
  gamma i := k.gamma i + l.gamma i

theorem catalyticCurrent_ratesAdd {n : ℕ} (k l : Rates n)
    (x : State n) :
    catalyticCurrent (ratesAdd k l) x =
      catalyticCurrent k x + catalyticCurrent l x := by
  funext i
  simp only [Pi.add_apply, catalyticCurrent, ratesAdd]
  ring

theorem loadedRestrictedField_ratesAdd {n : ℕ}
    (ET FT ST : ℝ) (k l : Rates n) (u : CoordinateSpace n) :
    loadedRestrictedField ET FT ST (ratesAdd k l) u =
      loadedRestrictedField ET FT ST k u +
      loadedRestrictedField ET FT ST l u := by
  apply Prod.ext
  · funext i
    simp only [Prod.add_def, Pi.add_apply]
    rw [loadedRestrictedField_slow_eq_incidence,
      loadedRestrictedField_slow_eq_incidence,
      loadedRestrictedField_slow_eq_incidence,
      catalyticCurrent_ratesAdd, Matrix.mulVec_add]
    rfl
  · apply Prod.ext
    · funext i
      simp only [loadedRestrictedField, toLoadedCoord,
        restrictedFieldEuclid, restrictedField, toCoordinateSpace,
        chart, field, kinaseNet, ratesAdd, Prod.add_def,
        Pi.add_apply]
      ring
    · funext i
      simp only [loadedRestrictedField, toLoadedCoord,
        restrictedFieldEuclid, restrictedField, toCoordinateSpace,
        chart, field, phosphataseNet, ratesAdd, Prod.add_def,
        Pi.add_apply]
      ring

/-- Around an arbitrary base rate list, the explicit three-list family
has exactly the same linear velocity response. -/
theorem loadedRestrictedField_translated_variation {n : ℕ}
    (ET FT ST : ℝ) (k : Rates n) (u : CoordinateSpace n)
    (hx : (stateFromLoaded ET FT ST u).Positive)
    (v : CoordinateSpace n) :
    loadedRestrictedField ET FT ST
      (ratesAdd k (rateVariation (stateFromLoaded ET FT ST u)
        v.2.1 v.2.2 v.1)) u =
      loadedRestrictedField ET FT ST k u + rateVariationResponse n v := by
  rw [loadedRestrictedField_ratesAdd]
  exact congrArg (loadedRestrictedField ET FT ST k u + ·)
    (rateVariationParameterField_eq_response ET FT ST u hx v)

/-- Surjective parameter derivative for a literal rate family translated
to any prescribed base rate list. -/
theorem translated_rateVariation_fderiv_surjective {n : ℕ}
    (ET FT ST : ℝ) (k : Rates n) (u v : CoordinateSpace n)
    (hx : (stateFromLoaded ET FT ST u).Positive) :
    Function.Surjective
      (fderiv ℝ (fun w : CoordinateSpace n =>
        loadedRestrictedField ET FT ST
          (ratesAdd k (rateVariation (stateFromLoaded ET FT ST u)
            w.2.1 w.2.2 w.1)) u) v) := by
  have hfun : (fun w : CoordinateSpace n =>
        loadedRestrictedField ET FT ST
          (ratesAdd k (rateVariation (stateFromLoaded ET FT ST u)
            w.2.1 w.2.2 w.1)) u) =
      (fun w => loadedRestrictedField ET FT ST k u +
        rateVariationResponse n w) := by
    funext w
    exact loadedRestrictedField_translated_variation ET FT ST k u hx w
  rw [hfun, fderiv_const_add]
  change Function.Surjective
    (fderiv ℝ (rateVariationResponse n).toContinuousLinearMap v)
  rw [ContinuousLinearMap.fderiv]
  exact rateVariationResponse_surjective n

end
end PhosphorylationStableCapacity
