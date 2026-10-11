module
public import proofs.PhosphorylationStableCapacity.LocalStableEquilibriumBudget
public import proofs.PhosphorylationStableCapacity.SplitJacobianContinuity
public import Mathlib.Analysis.Calculus.ContDiff.RCLike

@[expose] public section

namespace PhosphorylationStableCapacity

open PhosphorylationSharpness

noncomputable section

/-- The exact fixed-rate class field is continuously differentiable,
as a slice of the jointly smooth literal mass-action field. -/
theorem contDiff_restrictedFieldEuclid_fixed_rates {n : ℕ}
    (ET FT ST : ℝ) (k : Rates n) :
    ContDiff ℝ 1 (restrictedFieldEuclid ET FT ST k) := by
  have hslice : ContDiff ℝ 1
      (fun u : CoordinateSpace n =>
        ((rateVector k, u) : RateVector n × CoordinateSpace n)) := by
    fun_prop
  have hfield :=
    ((contDiff_jointRestrictedField (n := n) ET FT ST).of_le
      (by norm_num)).comp hslice
  change ContDiff ℝ 1 (fun u : CoordinateSpace n =>
    toCoordinateSpace (restrictedField ET FT ST k (ofCoordinateSpace u)))
  simpa [jointRestrictedField, restrictedFieldEuclid,
    ratesFromVector_rateVector, Function.comp_def] using hfield

/-- Local Lipschitz continuity needed for uniqueness and the
class-relative ODE flow. -/
theorem restrictedFieldEuclid_locallyLipschitz {n : ℕ}
    (ET FT ST : ℝ) (k : Rates n) :
    LocallyLipschitz (restrictedFieldEuclid ET FT ST k) :=
  (contDiff_restrictedFieldEuclid_fixed_rates ET FT ST k).locallyLipschitz

end
end PhosphorylationStableCapacity
