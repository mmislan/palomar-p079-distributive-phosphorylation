module
public import Mathlib.Analysis.Calculus.Deriv.Prod
public import proofs.PhosphorylationStableCapacity.CoalescedProjectedFastDerivativeC
public import proofs.PhosphorylationStableCapacity.CoalescedProjectedFastDerivativeD

@[expose] public section

namespace PhosphorylationStableCapacity

open Filter PhosphorylationSharpness

noncomputable section

/-- The entire fast component of the literal loaded class field has zero
derivative along each projected zero-sum coalesced inverse-response path.
This is the actual model-specific fast-tangent input for Schur elimination. -/
theorem coalescedProjectedFast_eventually_hasDerivAt_zero (m : ℕ) :
    ∀ᶠ r : ℝ in atTop,
      ∀ (q : Fin (m + 3) → ℝ),
        (∑ k, q k) = 0 →
        HasDerivAt (fun t : ℝ =>
          (loadedRestrictedField (2 * r) 2 (2 * (r + 1))
            (coalescedFiniteRates (m + 1) r)
            (loadedCoordOfState
              (bindingState (2 * r) 2
                (coalescedBindingP m r) (coalescedBindingQ m r)
                (bindingLinearPath (coalescedFiniteState (m + 1) r).S
                  (coalescedInverseResponse m r q) t)))).2)
          (0 : (Fin (m + 2) → ℝ) × (Fin (m + 2) → ℝ)) 0 := by
  filter_upwards [coalescedProjectedFastC_eventually_hasDerivAt_zero m,
    coalescedProjectedFastD_eventually_hasDerivAt_zero m]
    with r hC hD
  intro q hq
  have hc : HasDerivAt (fun t : ℝ =>
      (loadedRestrictedField (2 * r) 2 (2 * (r + 1))
        (coalescedFiniteRates (m + 1) r)
        (loadedCoordOfState
          (bindingState (2 * r) 2
            (coalescedBindingP m r) (coalescedBindingQ m r)
            (bindingLinearPath (coalescedFiniteState (m + 1) r).S
              (coalescedInverseResponse m r q) t)))).2.1)
      (0 : Fin (m + 2) → ℝ) 0 := by
    apply hasDerivAt_pi.mpr
    intro i
    simpa using hC q hq i
  have hd : HasDerivAt (fun t : ℝ =>
      (loadedRestrictedField (2 * r) 2 (2 * (r + 1))
        (coalescedFiniteRates (m + 1) r)
        (loadedCoordOfState
          (bindingState (2 * r) 2
            (coalescedBindingP m r) (coalescedBindingQ m r)
            (bindingLinearPath (coalescedFiniteState (m + 1) r).S
              (coalescedInverseResponse m r q) t)))).2.2)
      (0 : Fin (m + 2) → ℝ) 0 := by
    apply hasDerivAt_pi.mpr
    intro i
    simpa using hD q i
  convert hc.prodMk hd using 1

end
end PhosphorylationStableCapacity
