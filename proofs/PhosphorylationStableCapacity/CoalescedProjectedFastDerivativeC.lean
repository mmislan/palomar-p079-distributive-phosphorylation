module
public import proofs.PhosphorylationStableCapacity.LoadedProjectionFastDerivativeC
public import proofs.PhosphorylationStableCapacity.LoadedStateChartDerivative
public import proofs.PhosphorylationStableCapacity.BindingStatePathDerivatives
public import proofs.PhosphorylationStableCapacity.CoalescedBindingClassTangent
public import proofs.PhosphorylationStableCapacity.CoalescedBindingFastBalance

@[expose] public section

namespace PhosphorylationStableCapacity

open Filter PhosphorylationSharpness

noncomputable section

/-- Along every zero-sum inverse-response direction, the actual coalesced
loaded kinase-complex row has zero derivative for all sufficiently large
source parameters. The level-zero free substrate is handled by the
verified all-three-totals class tangent. -/
theorem coalescedProjectedFastC_eventually_hasDerivAt_zero (m : ℕ) :
    ∀ᶠ r : ℝ in atTop,
      ∀ (q : Fin (m + 3) → ℝ),
        (∑ k, q k) = 0 →
        ∀ i : Fin (m + 2),
          HasDerivAt (fun t : ℝ =>
            (loadedRestrictedField (2 * r) 2 (2 * (r + 1))
              (coalescedFiniteRates (m + 1) r)
              (loadedCoordOfState
                (bindingState (2 * r) 2
                  (coalescedBindingP m r) (coalescedBindingQ m r)
                  (bindingLinearPath (coalescedFiniteState (m + 1) r).S
                    (coalescedInverseResponse m r q) t)))).2.1 i) 0 0 := by
  filter_upwards [coalescedBindingPath_allTotals_eventually_hasDerivAt_zero m,
    coalescedBindingDenominators_eventually_ne_zero m,
    coalescedBindingState_eventually_eq_finiteState m,
    coalescedFiniteState_eventually_equilibrium (m + 1)]
    with r hclass hden hstate hsource
  obtain ⟨_, hpos, heq, htotalE, htotalF, htotalS⟩ := hsource
  intro q hq i
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
  have hbase : InClass (2 * r) 2 (2 * (r + 1)) (x 0) := by
    change InClass (2 * r) 2 (2 * (r + 1))
      (bindingState (2 * r) 2
        (coalescedBindingP m r) (coalescedBindingQ m r)
        (bindingLinearPath (coalescedFiniteState (m + 1) r).S
          (coalescedInverseResponse m r q) 0))
    rw [hpath0, hstate]
    exact ⟨htotalE, htotalF, htotalS⟩
  let dS : ℝ := (coalescedFiniteState (m + 1) r).S i.castSucc *
    (coalescedInverseResponse m r q) i.castSucc
  have hS : HasDerivAt (fun t : ℝ => (x t).S i.castSucc) dS 0 := by
    change HasDerivAt (fun t : ℝ =>
      bindingLinearPath (coalescedFiniteState (m + 1) r).S
        (coalescedInverseResponse m r q) t i.castSucc) dS 0
    exact bindingLinearPath_hasDerivAt _ _ i.castSucc
  have hTS : HasDerivAt (fun t : ℝ => totalS (x t)) 0 0 :=
    (hclass q hq).2.2
  have hprojS : HasDerivAt (fun t : ℝ =>
      (stateFromLoaded (2 * r) 2 (2 * (r + 1))
        (loadedCoordOfState (x t))).S i.castSucc) dS 0 := by
    by_cases hz : i.castSucc = 0
    · have hS0 : HasDerivAt (fun t : ℝ => (x t).S 0) dS 0 := by
        simpa only [hz] using hS
      have hp := stateFromLoaded_projection_S_zero_hasDerivAt
        (2 * r) 2 (2 * (r + 1)) x dS hS0 hTS
      simpa only [hz] using hp
    · obtain ⟨j, hj⟩ := Fin.exists_succ_eq_of_ne_zero hz
      rw [← hj] at hS ⊢
      simpa only [stateFromLoaded_loadedCoordOfState_S_succ] using hS
  have hE : HasDerivAt (fun t : ℝ => (x t).E)
      (-(2 * r * bindingWeightedTangent (coalescedBindingP m r)
          (coalescedFiniteState (m + 1) r).S
          (coalescedInverseResponse m r q)) /
        (bindingDenominator (coalescedBindingP m r)
          (coalescedFiniteState (m + 1) r).S) ^ 2) 0 := by
    change HasDerivAt (fun t : ℝ =>
      (2 * r) / bindingDenominator (coalescedBindingP m r)
        (bindingLinearPath (coalescedFiniteState (m + 1) r).S
          (coalescedInverseResponse m r q) t)) _ 0
    exact bindingFree_hasDerivAt_linearPath _ _ _ _ hden.1
  have hfast : ∀ t : ℝ,
      (field (coalescedFiniteRates (m + 1) r) (x t)).C i = 0 := by
    intro t
    exact (coalescedBindingState_fast_zero m r hpos heq _ i).1
  exact loadedProjectionFastField_C_hasDerivAt_zero
    (2 * r) 2 (2 * (r + 1)) (coalescedFiniteRates (m + 1) r)
    x i dS _ hbase (hclass q hq).1 hS hprojS hE hfast

end
end PhosphorylationStableCapacity
