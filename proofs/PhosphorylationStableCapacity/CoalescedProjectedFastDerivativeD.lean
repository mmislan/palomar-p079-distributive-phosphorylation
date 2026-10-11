module
public import proofs.PhosphorylationStableCapacity.LoadedProjectionFastDerivativeD
public import proofs.PhosphorylationStableCapacity.BindingStatePathDerivatives
public import proofs.PhosphorylationStableCapacity.CoalescedBindingClassTangent
public import proofs.PhosphorylationStableCapacity.CoalescedBindingFastBalance

@[expose] public section

namespace PhosphorylationStableCapacity

open Filter PhosphorylationSharpness

noncomputable section

/-- For every sufficiently large coalesced source parameter, the literal
loaded phosphatase-complex row has zero derivative along every projected
inverse-response binding path. -/
theorem coalescedProjectedFastD_eventually_hasDerivAt_zero (m : ℕ) :
    ∀ᶠ r : ℝ in atTop,
      ∀ (q : Fin (m + 3) → ℝ) (i : Fin (m + 2)),
        HasDerivAt (fun t : ℝ =>
          (loadedRestrictedField (2 * r) 2 (2 * (r + 1))
            (coalescedFiniteRates (m + 1) r)
            (loadedCoordOfState
              (bindingState (2 * r) 2
                (coalescedBindingP m r) (coalescedBindingQ m r)
                (bindingLinearPath (coalescedFiniteState (m + 1) r).S
                  (coalescedInverseResponse m r q) t)))).2.2 i) 0 0 := by
  filter_upwards [coalescedBindingPath_enzymeTotals_eventually_hasDerivAt_zero m,
    coalescedBindingState_eventually_eq_finiteState m,
    coalescedFiniteState_eventually_equilibrium (m + 1)]
    with r henz hstate hsource
  obtain ⟨_, hpos, heq, _, hF, _⟩ := hsource
  intro q i
  let x : ℝ → State (m + 2) := fun t =>
    bindingState (2 * r) 2
      (coalescedBindingP m r) (coalescedBindingQ m r)
      (bindingLinearPath (coalescedFiniteState (m + 1) r).S
        (coalescedInverseResponse m r q) t)
  have hpath0 : bindingLinearPath (coalescedFiniteState (m + 1) r).S
      (coalescedInverseResponse m r q) 0 =
        (coalescedFiniteState (m + 1) r).S := by
    funext j
    simp [bindingLinearPath]
  have hbase : totalF (x 0) = 2 := by
    change totalF (bindingState (2 * r) 2
      (coalescedBindingP m r) (coalescedBindingQ m r)
      (bindingLinearPath (coalescedFiniteState (m + 1) r).S
        (coalescedInverseResponse m r q) 0)) = 2
    rw [hpath0, hstate]
    exact hF
  have hS : HasDerivAt (fun t : ℝ => (x t).S i.succ)
      ((coalescedFiniteState (m + 1) r).S i.succ *
        (coalescedInverseResponse m r q) i.succ) 0 := by
    change HasDerivAt (fun t : ℝ =>
      bindingLinearPath (coalescedFiniteState (m + 1) r).S
        (coalescedInverseResponse m r q) t i.succ) _ 0
    exact bindingLinearPath_hasDerivAt _ _ i.succ
  have hfast : ∀ t : ℝ,
      (field (coalescedFiniteRates (m + 1) r) (x t)).D i = 0 := by
    intro t
    exact (coalescedBindingState_fast_zero m r hpos heq _ i).2
  exact loadedProjectionFastField_D_hasDerivAt_zero
    (2 * r) 2 (2 * (r + 1)) (coalescedFiniteRates (m + 1) r)
    x i _ hbase (henz q).2 hS hfast

end
end PhosphorylationStableCapacity
