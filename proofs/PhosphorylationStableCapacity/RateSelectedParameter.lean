module
public import proofs.PhosphorylationStableCapacity.RateVariationPositiveNeighborhood

@[expose] public section

namespace PhosphorylationStableCapacity

open PhosphorylationSharpness Matrix

noncomputable section

/-- The `3n` rate coordinates used for the regularity perturbation:
kinase binding, kinase catalysis, and phosphatase binding. -/
def selectedRates {n : ℕ} (v : CoordinateSpace n) : Rates n where
  a := v.1
  b _ := 0
  c := v.2.1
  alpha := v.2.2
  beta _ := 0
  gamma _ := 0

/-- A literal right inverse of the selected-rate response at a state.
The path-incidence inverse prescribes catalytic currents; the remaining
two lists prescribe complex velocities. -/
def selectedRateRightInverse {n : ℕ} (x : State n)
    (y : CoordinateSpace n) : CoordinateSpace n :=
  let r := (projectedPathIncidence n)⁻¹.mulVec y.1
  (fun i => (y.2.1 i + r i) / (x.S i.castSucc * x.E),
   fun i => r i / x.C i,
   fun i => y.2.2 i / (x.S i.succ * x.F))

theorem selectedRates_rightInverse_eq_rateVariation {n : ℕ}
    (x : State n) (y : CoordinateSpace n) :
    selectedRates (selectedRateRightInverse x y) =
      rateVariation x y.2.1 y.2.2
        ((projectedPathIncidence n)⁻¹.mulVec y.1) := by
  rfl

theorem selectedRates_response_right_inverse {n : ℕ}
    (ET FT ST : ℝ) (u y : CoordinateSpace n)
    (hx : (stateFromLoaded ET FT ST u).Positive) :
    loadedRestrictedField ET FT ST
      (selectedRates (selectedRateRightInverse
        (stateFromLoaded ET FT ST u) y)) u = y := by
  let x := stateFromLoaded ET FT ST u
  let r := (projectedPathIncidence n)⁻¹.mulVec y.1
  rw [selectedRates_rightInverse_eq_rateVariation]
  apply Prod.ext
  · rw [loadedRestrictedField_slow_eq_incidence]
    have hc : catalyticCurrent (rateVariation x y.2.1 y.2.2 r) x = r := by
      funext i
      exact rateVariation_current x hx y.2.1 y.2.2 r i
    rw [show catalyticCurrent (rateVariation x y.2.1 y.2.2 r)
      (stateFromLoaded ET FT ST u) = r from hc]
    change (projectedPathIncidence n).mulVec
      ((projectedPathIncidence n)⁻¹.mulVec y.1) = y.1
    rw [Matrix.mulVec_mulVec,
      Matrix.mul_nonsing_inv _ (by
        rw [projectedPathIncidence_det]
        exact isUnit_one), Matrix.one_mulVec]
  · apply Prod.ext
    · funext i
      simpa [loadedRestrictedField, restrictedFieldEuclid,
        restrictedField, chart, toLoadedCoord, toCoordinateSpace,
        stateFromLoaded, x, r] using
        rateVariation_C x hx y.2.1 y.2.2 r i
    · funext i
      simpa [loadedRestrictedField, restrictedFieldEuclid,
        restrictedField, chart, toLoadedCoord, toCoordinateSpace,
        stateFromLoaded, x, r] using
        rateVariation_D x hx y.2.1 y.2.2 r i

end
end PhosphorylationStableCapacity
