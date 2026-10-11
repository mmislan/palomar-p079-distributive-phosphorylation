module
public import proofs.PhosphorylationStableCapacity.EdgeScaledBindingCurrentDerivative
public import proofs.PhosphorylationStableCapacity.CoalescedInverseCurrentDerivative

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section

open Filter PhosphorylationSharpness

/-- Apply an arbitrary edge-current vector to the coalesced source while
preserving the same literal state and totals. -/
def coalescedAllScaledRates (m : ℕ) (r : ℝ)
    (w : Fin (m+2) → ℝ) : Rates (m+2) :=
  edgeScaledRates w (coalescedFiniteRates (m+1) r)

/-- The current derivative along every inverse-response direction scales
by its own edge factor, with no relation among the factors. -/
theorem coalescedAllEdgeScaledCurrent_eventually_hasDerivAt (m : ℕ) :
    ∀ᶠ r : ℝ in atTop,
      ∀ (w : Fin (m+2) → ℝ) (q : Fin (m+3) → ℝ)
        (i : Fin (m+2)),
        HasDerivAt (fun t : ℝ =>
          bindingCatalyticCurrent (2*r) 2
            (coalescedBindingP m r) (coalescedBindingQ m r)
            Fin.castSucc Fin.succ
            (coalescedAllScaledRates m r w).c
            (coalescedAllScaledRates m r w).gamma
            (bindingLinearPath (coalescedFiniteState (m+1) r).S
              (coalescedInverseResponse m r q) t) i)
          (w i * (coalescedCurrentJacobianMatrix m r).mulVec
            (coalescedInverseResponse m r q) i) 0 := by
  filter_upwards [coalescedInverseCurrent_eventually_hasDerivAt m]
    with r hcurrent
  intro w q i
  have h := (hcurrent q i).const_mul (w i)
  simpa only [coalescedAllScaledRates, edgeScaledRates,
    edgeScaled_bindingCatalyticCurrent] using h

end

end PhosphorylationStableCapacity
