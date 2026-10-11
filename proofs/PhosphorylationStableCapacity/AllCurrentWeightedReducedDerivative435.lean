module
public import proofs.PhosphorylationStableCapacity.AllCurrentWeightedDerivative435
public import proofs.PhosphorylationStableCapacity.LoadedReducedField

@[expose] public section

namespace PhosphorylationStableCapacity

open Filter PhosphorylationSharpness

noncomputable section

/-- The literal reduced slow-field derivative under final-edge retuning
is path incidence applied to the edge-weighted finite current response. -/
theorem coalescedAllInverseReducedSlow_eventually_hasDerivAt
    (m : ℕ) :
    ∀ᶠ r : ℝ in atTop,
      ∀ (w : Fin (m + 2) → ℝ) (q : Fin (m + 3) → ℝ) (j : Fin (m + 3)),
        HasDerivAt (fun t : ℝ =>
          bindingReducedSlowField (2 * r) 2
            (coalescedBindingP m r) (coalescedBindingQ m r)
            (coalescedAllScaledRates m r w)
            (bindingLinearPath (coalescedFiniteState (m + 1) r).S
              (coalescedInverseResponse m r q) t) j)
          (∑ i : Fin (m + 2),
            ((if i.succ = j then
              w i *
                (coalescedCurrentJacobianMatrix m r).mulVec
                  (coalescedInverseResponse m r q) i else 0) -
             (if i.castSucc = j then
              w i *
                (coalescedCurrentJacobianMatrix m r).mulVec
                  (coalescedInverseResponse m r q) i else 0))) 0 := by
  filter_upwards [coalescedAllEdgeScaledCurrent_eventually_hasDerivAt m]
    with r hcurrent
  intro w q j
  have hsum : HasDerivAt (fun t : ℝ =>
      ∑ i : Fin (m + 2),
        ((if i.succ = j then
          bindingCatalyticCurrent (2 * r) 2
            (coalescedBindingP m r) (coalescedBindingQ m r)
            Fin.castSucc Fin.succ
            (coalescedAllScaledRates m r w).c
            (coalescedAllScaledRates m r w).gamma
            (bindingLinearPath (coalescedFiniteState (m + 1) r).S
              (coalescedInverseResponse m r q) t) i else 0) -
         (if i.castSucc = j then
          bindingCatalyticCurrent (2 * r) 2
            (coalescedBindingP m r) (coalescedBindingQ m r)
            Fin.castSucc Fin.succ
            (coalescedAllScaledRates m r w).c
            (coalescedAllScaledRates m r w).gamma
            (bindingLinearPath (coalescedFiniteState (m + 1) r).S
              (coalescedInverseResponse m r q) t) i else 0)))
      (∑ i : Fin (m + 2),
        ((if i.succ = j then
          w i *
            (coalescedCurrentJacobianMatrix m r).mulVec
              (coalescedInverseResponse m r q) i else 0) -
         (if i.castSucc = j then
          w i *
            (coalescedCurrentJacobianMatrix m r).mulVec
              (coalescedInverseResponse m r q) i else 0))) 0 := by
    apply HasDerivAt.fun_sum
    intro i _
    have hcur := hcurrent w q i
    have hright : HasDerivAt (fun t : ℝ =>
        if i.succ = j then
          bindingCatalyticCurrent (2 * r) 2
            (coalescedBindingP m r) (coalescedBindingQ m r)
            Fin.castSucc Fin.succ
            (coalescedAllScaledRates m r w).c
            (coalescedAllScaledRates m r w).gamma
            (bindingLinearPath (coalescedFiniteState (m + 1) r).S
              (coalescedInverseResponse m r q) t) i else 0)
        (if i.succ = j then
          w i *
            (coalescedCurrentJacobianMatrix m r).mulVec
              (coalescedInverseResponse m r q) i else 0) 0 := by
      by_cases hj : i.succ = j
      · simpa [hj] using hcur
      · simpa [hj] using (hasDerivAt_const (0 : ℝ) (0 : ℝ))
    have hleft : HasDerivAt (fun t : ℝ =>
        if i.castSucc = j then
          bindingCatalyticCurrent (2 * r) 2
            (coalescedBindingP m r) (coalescedBindingQ m r)
            Fin.castSucc Fin.succ
            (coalescedAllScaledRates m r w).c
            (coalescedAllScaledRates m r w).gamma
            (bindingLinearPath (coalescedFiniteState (m + 1) r).S
              (coalescedInverseResponse m r q) t) i else 0)
        (if i.castSucc = j then
          w i *
            (coalescedCurrentJacobianMatrix m r).mulVec
              (coalescedInverseResponse m r q) i else 0) 0 := by
      by_cases hj : i.castSucc = j
      · simpa [hj] using hcur
      · simpa [hj] using (hasDerivAt_const (0 : ℝ) (0 : ℝ))
    exact hright.sub hleft
  simpa only [bindingReducedSlowField_eq_current_sum] using hsum

end
end PhosphorylationStableCapacity
