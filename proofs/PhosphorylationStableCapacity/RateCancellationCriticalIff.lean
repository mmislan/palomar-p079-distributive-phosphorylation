module
public import proofs.PhosphorylationStableCapacity.RateCancellationJacobianBridge
public import Mathlib.MeasureTheory.Function.Jacobian

@[expose] public section

namespace PhosphorylationStableCapacity

open PhosphorylationSharpness

noncomputable section

/-- A positive equilibrium has a singular class Jacobian exactly when
its cancellation-graph derivative is noninjective. -/
theorem cancellationParameter_fderiv_injective_iff {n : ℕ}
    (ET FT ST : ℝ) (k : Rates n) (u v : CoordinateSpace n)
    (hx : (stateFromLoaded ET FT ST u).Positive)
    (hzero : loadedRestrictedField ET FT ST
      (ratesAdd k (selectedRates v)) u = 0) :
    Function.Injective (fderiv ℝ (cancellationParameter ET FT ST k) u) ↔
      Function.Injective (fderiv ℝ
        (loadedRestrictedField ET FT ST (ratesAdd k (selectedRates v))) u) := by
  let B := (selectedRateRightInverseLinear
    (stateFromLoaded ET FT ST u)).toContinuousLinearMap
  let J := fderiv ℝ
    (loadedRestrictedField ET FT ST (ratesAdd k (selectedRates v))) u
  have hB : Function.Injective B :=
    (selectedRateRightInverseLinear_bijective ET FT ST u hx).1
  have hbridge := cancellationParameter_fderiv_eq_inverse_jacobian
    ET FT ST k u v hx hzero
  change fderiv ℝ (cancellationParameter ET FT ST k) u =
    -(B.comp J) at hbridge
  rw [hbridge]
  constructor
  · intro hinj a b hab
    apply hinj
    simpa [J, ContinuousLinearMap.comp_apply] using
      congrArg (fun z : CoordinateSpace n => -(B z)) hab
  · intro hinj a b hab
    apply hinj
    apply hB
    have hneg : -(B (J a)) = -(B (J b)) := by
      simpa [ContinuousLinearMap.comp_apply] using hab
    exact neg_injective hneg

/-- The exact critical-point condition needed for fixed-dimension Sard:
the graph derivative has zero determinant iff the literal class
Jacobian does. -/
theorem cancellationParameter_critical_iff_jacobian_singular {n : ℕ}
    (ET FT ST : ℝ) (k : Rates n) (u v : CoordinateSpace n)
    (hx : (stateFromLoaded ET FT ST u).Positive)
    (hzero : loadedRestrictedField ET FT ST
      (ratesAdd k (selectedRates v)) u = 0) :
    (fderiv ℝ (cancellationParameter ET FT ST k) u).det = 0 ↔
      (fderiv ℝ
        (loadedRestrictedField ET FT ST (ratesAdd k (selectedRates v))) u).det = 0 := by
  simpa [ContinuousLinearMap.det,
    LinearMap.det_eq_zero_iff_ker_ne_bot, ne_eq,
    LinearMap.ker_eq_bot] using
    not_congr (cancellationParameter_fderiv_injective_iff
      ET FT ST k u v hx hzero)

end
end PhosphorylationStableCapacity
