module
public import proofs.PhosphorylationStableCapacity.EdgeScaledBindingCurrentDerivative
public import proofs.PhosphorylationStableCapacity.LoadedReducedField

@[expose] public section

namespace PhosphorylationStableCapacity

open Filter PhosphorylationSharpness

noncomputable section

/-- The literal reduced slow-field derivative under final-edge retuning
is path incidence applied to the edge-weighted finite current response. -/
theorem coalescedWeightedInverseReducedSlow_eventually_hasDerivAt
    (m : ℕ) :
    ∀ᶠ r : ℝ in atTop,
      ∀ (τ : ℝ) (q : Fin (m + 3) → ℝ) (j : Fin (m + 3)),
        HasDerivAt (fun t : ℝ =>
          bindingReducedSlowField (2 * r) 2
            (coalescedBindingP m r) (coalescedBindingQ m r)
            (coalescedFinalScaledRates m r τ)
            (bindingLinearPath (coalescedFiniteState (m + 1) r).S
              (coalescedInverseResponse m r q) t) j)
          (∑ i : Fin (m + 2),
            ((if i.succ = j then
              coalescedFinalCurrentWeights m τ i *
                (coalescedCurrentJacobianMatrix m r).mulVec
                  (coalescedInverseResponse m r q) i else 0) -
             (if i.castSucc = j then
              coalescedFinalCurrentWeights m τ i *
                (coalescedCurrentJacobianMatrix m r).mulVec
                  (coalescedInverseResponse m r q) i else 0))) 0 := by
  filter_upwards [coalescedEdgeScaledCurrent_eventually_hasDerivAt m]
    with r hcurrent
  intro τ q j
  have hsum : HasDerivAt (fun t : ℝ =>
      ∑ i : Fin (m + 2),
        ((if i.succ = j then
          bindingCatalyticCurrent (2 * r) 2
            (coalescedBindingP m r) (coalescedBindingQ m r)
            Fin.castSucc Fin.succ
            (coalescedFinalScaledRates m r τ).c
            (coalescedFinalScaledRates m r τ).gamma
            (bindingLinearPath (coalescedFiniteState (m + 1) r).S
              (coalescedInverseResponse m r q) t) i else 0) -
         (if i.castSucc = j then
          bindingCatalyticCurrent (2 * r) 2
            (coalescedBindingP m r) (coalescedBindingQ m r)
            Fin.castSucc Fin.succ
            (coalescedFinalScaledRates m r τ).c
            (coalescedFinalScaledRates m r τ).gamma
            (bindingLinearPath (coalescedFiniteState (m + 1) r).S
              (coalescedInverseResponse m r q) t) i else 0)))
      (∑ i : Fin (m + 2),
        ((if i.succ = j then
          coalescedFinalCurrentWeights m τ i *
            (coalescedCurrentJacobianMatrix m r).mulVec
              (coalescedInverseResponse m r q) i else 0) -
         (if i.castSucc = j then
          coalescedFinalCurrentWeights m τ i *
            (coalescedCurrentJacobianMatrix m r).mulVec
              (coalescedInverseResponse m r q) i else 0))) 0 := by
    apply HasDerivAt.fun_sum
    intro i _
    have hcur := hcurrent τ q i
    have hright : HasDerivAt (fun t : ℝ =>
        if i.succ = j then
          bindingCatalyticCurrent (2 * r) 2
            (coalescedBindingP m r) (coalescedBindingQ m r)
            Fin.castSucc Fin.succ
            (coalescedFinalScaledRates m r τ).c
            (coalescedFinalScaledRates m r τ).gamma
            (bindingLinearPath (coalescedFiniteState (m + 1) r).S
              (coalescedInverseResponse m r q) t) i else 0)
        (if i.succ = j then
          coalescedFinalCurrentWeights m τ i *
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
            (coalescedFinalScaledRates m r τ).c
            (coalescedFinalScaledRates m r τ).gamma
            (bindingLinearPath (coalescedFiniteState (m + 1) r).S
              (coalescedInverseResponse m r q) t) i else 0)
        (if i.castSucc = j then
          coalescedFinalCurrentWeights m τ i *
            (coalescedCurrentJacobianMatrix m r).mulVec
              (coalescedInverseResponse m r q) i else 0) 0 := by
      by_cases hj : i.castSucc = j
      · simpa [hj] using hcur
      · simpa [hj] using (hasDerivAt_const (0 : ℝ) (0 : ℝ))
    exact hright.sub hleft
  simpa only [bindingReducedSlowField_eq_current_sum] using hsum

end
end PhosphorylationStableCapacity
