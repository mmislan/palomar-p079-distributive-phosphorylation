module
public import Mathlib.Analysis.Calculus.Deriv.Prod
public import proofs.PhosphorylationStableCapacity.CoalescedArbitraryInventoryDerivative
public import proofs.PhosphorylationStableCapacity.CoalescedBindingClassTangent
public import proofs.PhosphorylationStableCapacity.LoadedStateChartBridge

@[expose] public section

namespace PhosphorylationStableCapacity

open Filter PhosphorylationSharpness

noncomputable section

/-- The exact raw bound-complex derivative along a logarithmic free-
substrate path. -/
def bindingComplexRawTangent {ι : Type*} [Fintype ι]
    (ET : ℝ) (p S σ : ι → ℝ) (i : ι) : ℝ :=
  ((ET * p i * S i * σ i) * bindingDenominator p S -
      (ET * p i * S i) * bindingWeightedTangent p S σ) /
    (bindingDenominator p S) ^ 2

/-- The actual loaded coordinate tangent of the coalesced binding path.
Its slow part is the prescribed loaded forcing; its two fast parts are
literal bound-complex derivatives. -/
def coalescedBindingCoordTangent (m : ℕ) (r : ℝ)
    (q : Fin (m + 3) → ℝ) : CoordinateSpace (m + 2) :=
  (fun i => r * q i.succ,
    fun i => bindingComplexRawTangent (2 * r)
      (coalescedBindingP m r) (coalescedFiniteState (m + 1) r).S
      (coalescedInverseResponse m r q) i.castSucc,
    fun i => bindingComplexRawTangent 2
      (coalescedBindingQ m r) (coalescedFiniteState (m + 1) r).S
      (coalescedInverseResponse m r q) i.succ)

/-- For every sufficiently large source parameter, the literal binding
path is differentiable in the loaded class coordinates with exactly the
above tangent, for every inverse-response forcing. -/
theorem coalescedLoadedCoordPath_eventually_hasDerivAt (m : ℕ) :
    ∀ᶠ r : ℝ in atTop,
      ∀ q : Fin (m + 3) → ℝ,
        HasDerivAt (fun t : ℝ =>
          loadedCoordOfState (bindingState (2 * r) 2
            (coalescedBindingP m r) (coalescedBindingQ m r)
            (bindingLinearPath (coalescedFiniteState (m + 1) r).S
              (coalescedInverseResponse m r q) t)))
          (coalescedBindingCoordTangent m r q) 0 := by
  filter_upwards [coalescedLiteralInventory_eventually_hasDerivAt m,
    coalescedBindingDenominators_eventually_ne_zero m]
    with r hlevels hden
  intro q
  have hs : HasDerivAt (fun t : ℝ =>
      (loadedCoordOfState (bindingState (2 * r) 2
        (coalescedBindingP m r) (coalescedBindingQ m r)
        (bindingLinearPath (coalescedFiniteState (m + 1) r).S
          (coalescedInverseResponse m r q) t))).1)
      (coalescedBindingCoordTangent m r q).1 0 := by
    apply hasDerivAt_pi.mpr
    intro i
    simpa only [loadedCoordOfState_slow,
      coalescedBindingCoordTangent] using hlevels q i.succ
  have hc : HasDerivAt (fun t : ℝ =>
      (loadedCoordOfState (bindingState (2 * r) 2
        (coalescedBindingP m r) (coalescedBindingQ m r)
        (bindingLinearPath (coalescedFiniteState (m + 1) r).S
          (coalescedInverseResponse m r q) t))).2.1)
      (coalescedBindingCoordTangent m r q).2.1 0 := by
    apply hasDerivAt_pi.mpr
    intro i
    have h := bindingComplex_hasDerivAt_linearPath_raw
      (2 * r) (coalescedBindingP m r)
      (coalescedFiniteState (m + 1) r).S
      (coalescedInverseResponse m r q) i.castSucc hden.1
    simpa only [loadedCoordOfState_C, bindingState,
      coalescedBindingCoordTangent, bindingComplexRawTangent] using h
  have hd : HasDerivAt (fun t : ℝ =>
      (loadedCoordOfState (bindingState (2 * r) 2
        (coalescedBindingP m r) (coalescedBindingQ m r)
        (bindingLinearPath (coalescedFiniteState (m + 1) r).S
          (coalescedInverseResponse m r q) t))).2.2)
      (coalescedBindingCoordTangent m r q).2.2 0 := by
    apply hasDerivAt_pi.mpr
    intro i
    have h := bindingComplex_hasDerivAt_linearPath_raw
      2 (coalescedBindingQ m r)
      (coalescedFiniteState (m + 1) r).S
      (coalescedInverseResponse m r q) i.succ hden.2
    simpa only [loadedCoordOfState_D, bindingState,
      coalescedBindingCoordTangent, bindingComplexRawTangent] using h
  exact hs.prodMk (hc.prodMk hd)

end
end PhosphorylationStableCapacity
