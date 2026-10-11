module
public import proofs.PhosphorylationStableCapacity.PositivePrefixCurrents435
public import proofs.PhosphorylationStableCapacity.AllCurrentWeightedDerivative435
public import proofs.PhosphorylationStableCapacity.SplitJacobianContinuity

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section

open PhosphorylationSharpness

/-- Rate-vector continuity of the coalesced current family, without
the compact fast/slow spectral dependencies. -/
theorem continuous_coalescedAllCurrent_rateVector_light
    (m : ℕ) (r τ : ℝ) :
    Continuous (fun ω : PositivePrefixCurrents m =>
      rateVector (coalescedAllScaledRates m r
        (Fin.lastCases τ ω.val))) := by
  apply continuous_pi
  intro j
  apply continuous_pi
  intro i
  have hw : Continuous (fun ω : PositivePrefixCurrents m =>
      Fin.lastCases (motive := fun _ => ℝ) τ ω.val i) := by
    cases i using Fin.lastCases with
    | last => simpa only [Fin.lastCases_last] using (continuous_const : Continuous
        (fun _ : PositivePrefixCurrents m => τ))
    | cast i =>
        simpa only [Fin.lastCases_castSucc, Function.comp_def] using
          (continuous_apply i).comp continuous_subtype_val
  fin_cases j
  · change Continuous (fun ω : PositivePrefixCurrents m =>
      Fin.lastCases τ ω.val i * (coalescedFiniteRates (m+1) r).a i)
    exact hw.mul_const _
  · change Continuous (fun ω : PositivePrefixCurrents m =>
      Fin.lastCases τ ω.val i * (coalescedFiniteRates (m+1) r).b i)
    exact hw.mul_const _
  · change Continuous (fun ω : PositivePrefixCurrents m =>
      Fin.lastCases τ ω.val i * (coalescedFiniteRates (m+1) r).c i)
    exact hw.mul_const _
  · change Continuous (fun ω : PositivePrefixCurrents m =>
      Fin.lastCases τ ω.val i * (coalescedFiniteRates (m+1) r).alpha i)
    exact hw.mul_const _
  · change Continuous (fun ω : PositivePrefixCurrents m =>
      Fin.lastCases τ ω.val i * (coalescedFiniteRates (m+1) r).beta i)
    exact hw.mul_const _
  · change Continuous (fun ω : PositivePrefixCurrents m =>
      Fin.lastCases τ ω.val i * (coalescedFiniteRates (m+1) r).gamma i)
    exact hw.mul_const _

end

end PhosphorylationStableCapacity
