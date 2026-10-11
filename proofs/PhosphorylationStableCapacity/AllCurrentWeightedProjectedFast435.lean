module
public import proofs.PhosphorylationStableCapacity.AllCurrentWeightedDerivative435
public import proofs.PhosphorylationStableCapacity.CoalescedProjectedFastDerivative

@[expose] public section

namespace PhosphorylationStableCapacity

open Filter PhosphorylationSharpness

noncomputable section

/-- Per-edge retuning preserves the zero projected fast derivative along
every zero-sum inverse-response binding direction. -/
theorem coalescedAllProjectedFast_eventually_hasDerivAt_zero (m : ℕ) :
    ∀ᶠ r : ℝ in atTop,
      ∀ (w : Fin (m + 2) → ℝ) (q : Fin (m + 3) → ℝ),
        (∑ k, q k) = 0 →
        HasDerivAt (fun t : ℝ =>
          (loadedRestrictedField (2 * r) 2 (2 * (r + 1))
            (coalescedAllScaledRates m r w)
            (loadedCoordOfState
              (bindingState (2 * r) 2
                (coalescedBindingP m r) (coalescedBindingQ m r)
                (bindingLinearPath (coalescedFiniteState (m + 1) r).S
                  (coalescedInverseResponse m r q) t)))).2)
          (0 : (Fin (m + 2) → ℝ) × (Fin (m + 2) → ℝ)) 0 := by
  filter_upwards [coalescedProjectedFastC_eventually_hasDerivAt_zero m,
    coalescedProjectedFastD_eventually_hasDerivAt_zero m]
    with r hC hD
  intro w q hq
  have hc : HasDerivAt (fun t : ℝ =>
      (loadedRestrictedField (2 * r) 2 (2 * (r + 1))
        (coalescedAllScaledRates m r w)
        (loadedCoordOfState
          (bindingState (2 * r) 2
            (coalescedBindingP m r) (coalescedBindingQ m r)
            (bindingLinearPath (coalescedFiniteState (m + 1) r).S
              (coalescedInverseResponse m r q) t)))).2.1)
      (0 : Fin (m + 2) → ℝ) 0 := by
    apply hasDerivAt_pi.mpr
    intro i
    have h := (hC q hq i).const_mul (w i)
    convert h using 1 <;>
      simp only [coalescedAllScaledRates,
        edgeScaledRates_loadedRestrictedField_C, mul_zero, Pi.zero_apply]
  have hd : HasDerivAt (fun t : ℝ =>
      (loadedRestrictedField (2 * r) 2 (2 * (r + 1))
        (coalescedAllScaledRates m r w)
        (loadedCoordOfState
          (bindingState (2 * r) 2
            (coalescedBindingP m r) (coalescedBindingQ m r)
            (bindingLinearPath (coalescedFiniteState (m + 1) r).S
              (coalescedInverseResponse m r q) t)))).2.2)
      (0 : Fin (m + 2) → ℝ) 0 := by
    apply hasDerivAt_pi.mpr
    intro i
    have h := (hD q i).const_mul (w i)
    convert h using 1 <;>
      simp only [coalescedAllScaledRates,
        edgeScaledRates_loadedRestrictedField_D, mul_zero, Pi.zero_apply]
  convert hc.prodMk hd using 1

end
end PhosphorylationStableCapacity
