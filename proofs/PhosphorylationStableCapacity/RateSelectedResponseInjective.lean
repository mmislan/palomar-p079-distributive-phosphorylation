module
public import proofs.PhosphorylationStableCapacity.RateCancellationGraph

@[expose] public section

namespace PhosphorylationStableCapacity

open PhosphorylationSharpness Matrix

noncomputable section

/-- At a positive state, the selected `3n` rate coordinates uniquely
determine the loaded class velocity. -/
theorem selectedRates_response_injective {n : ℕ}
    (ET FT ST : ℝ) (u : CoordinateSpace n)
    (hx : (stateFromLoaded ET FT ST u).Positive) :
    Function.Injective
      (fun v : CoordinateSpace n =>
        loadedRestrictedField ET FT ST (selectedRates v) u) := by
  intro v w h
  change loadedRestrictedField ET FT ST (selectedRates v) u =
    loadedRestrictedField ET FT ST (selectedRates w) u at h
  let x := stateFromLoaded ET FT ST u
  rcases hx with ⟨hS, hE, hF, hC, _⟩
  have hslow := congrArg (fun z : CoordinateSpace n => z.1) h
  change (loadedRestrictedField ET FT ST (selectedRates v) u).1 =
    (loadedRestrictedField ET FT ST (selectedRates w) u).1 at hslow
  rw [loadedRestrictedField_slow_eq_incidence,
    loadedRestrictedField_slow_eq_incidence] at hslow
  have hcurrent : catalyticCurrent (selectedRates v) x =
      catalyticCurrent (selectedRates w) x :=
    (Matrix.mulVec_injective_of_isUnit
      (projectedPathIncidence_isUnit n)) hslow
  have hc (i : Fin n) : v.2.1 i = w.2.1 i := by
    have hi := congrFun hcurrent i
    simp only [catalyticCurrent, selectedRates, zero_mul, sub_zero] at hi
    exact (mul_right_cancel₀ (ne_of_gt (hC i))) hi
  have hd (i : Fin n) : v.2.2 i = w.2.2 i := by
    have hi := congrArg (fun z : CoordinateSpace n => z.2.2 i) h
    change (loadedRestrictedField ET FT ST (selectedRates v) u).2.2 i =
      (loadedRestrictedField ET FT ST (selectedRates w) u).2.2 i at hi
    rw [loadedFastField_D, loadedFastField_D] at hi
    simp only [selectedRates, zero_add, zero_mul, sub_zero] at hi
    have hSF : x.S i.succ * x.F ≠ 0 :=
      mul_ne_zero (ne_of_gt (hS _)) (ne_of_gt hF)
    apply mul_right_cancel₀ hSF
    nlinarith [hi]
  have ha (i : Fin n) : v.1 i = w.1 i := by
    have hi := congrArg (fun z : CoordinateSpace n => z.2.1 i) h
    change (loadedRestrictedField ET FT ST (selectedRates v) u).2.1 i =
      (loadedRestrictedField ET FT ST (selectedRates w) u).2.1 i at hi
    rw [loadedFastField_C, loadedFastField_C] at hi
    simp only [selectedRates, zero_add] at hi
    rw [hc i] at hi
    have hSE : x.S i.castSucc * x.E ≠ 0 :=
      mul_ne_zero (ne_of_gt (hS _)) (ne_of_gt hE)
    apply mul_right_cancel₀ hSE
    nlinarith [hi]
  apply Prod.ext
  · funext i
    exact ha i
  · apply Prod.ext
    · funext i
      exact hc i
    · funext i
      exact hd i

/-- In the positive class interior, the exact zero set of the selected
rate family is the graph of the explicit cancellation parameter. -/
theorem loadedField_zero_iff_parameter_eq_cancellation {n : ℕ}
    (ET FT ST : ℝ) (k : Rates n) (u v : CoordinateSpace n)
    (hx : (stateFromLoaded ET FT ST u).Positive) :
    loadedRestrictedField ET FT ST (ratesAdd k (selectedRates v)) u = 0 ↔
      v = cancellationParameter ET FT ST k u := by
  constructor
  · intro hv
    have hc := loadedField_cancellationParameter_zero ET FT ST k u hx
    rw [loadedRestrictedField_ratesAdd] at hv hc
    apply selectedRates_response_injective ET FT ST u hx
    exact add_left_cancel (hv.trans hc.symm)
  · intro hv
    rw [hv]
    exact loadedField_cancellationParameter_zero ET FT ST k u hx

end
end PhosphorylationStableCapacity
