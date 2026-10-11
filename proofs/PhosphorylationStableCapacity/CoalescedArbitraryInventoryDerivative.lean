module
public import proofs.PhosphorylationStableCapacity.CoalescedBindingLevelBridge
public import proofs.PhosphorylationStableCapacity.LoadedTotalIdentity

@[expose] public section

namespace PhosphorylationStableCapacity

open Filter PhosphorylationSharpness

noncomputable section

/-- The inverse response realizes any loaded-level forcing, at first order,
along the actual reversible-binding path. -/
theorem coalescedInventory_eventually_hasDerivAt (m : ℕ) :
    ∀ᶠ r : ℝ in atTop,
      ∀ (q : Fin (m + 3) → ℝ) (k : Fin (m + 3)),
        HasDerivAt (fun t : ℝ =>
          bindingLoadedLevel (2 * r) 2
            (coalescedBindingP m r) (coalescedBindingQ m r)
            (bindingLinearPath (coalescedFiniteState (m + 1) r).S
              (coalescedInverseResponse m r q) t) k)
          (r * q k) 0 := by
  filter_upwards [coalescedFullMass_eventually_hasDerivAt_bindingLevel m,
    coalescedFullMass_eventually_det_ne_zero m] with r hmass hdet
  intro q k
  have h := hmass (coalescedInverseResponse m r q) k
  have heq :
      (coalescedFullMass m r).mulVec
        (coalescedInverseResponse m r q) k = r * q k := by
    have hs := congrArg (fun f : Fin (m + 3) → ℝ => f k)
      (coalescedInverseResponse_mass_equation m r q hdet)
    simpa only [Pi.smul_apply, smul_eq_mul] using hs
  rw [heq] at h
  exact h

/-- The arbitrary inverse response changes the literal loaded levels by
the prescribed forcing. -/
theorem coalescedLiteralInventory_eventually_hasDerivAt (m : ℕ) :
    ∀ᶠ r : ℝ in atTop,
      ∀ (q : Fin (m + 3) → ℝ) (k : Fin (m + 3)),
        HasDerivAt (fun t : ℝ =>
          loadedLevel (bindingState (2 * r) 2
            (coalescedBindingP m r) (coalescedBindingQ m r)
            (bindingLinearPath (coalescedFiniteState (m + 1) r).S
              (coalescedInverseResponse m r q) t)) k)
          (r * q k) 0 := by
  filter_upwards [coalescedInventory_eventually_hasDerivAt m]
    with r hmass
  intro q k
  have h := hmass q k
  have hfun : (fun t : ℝ =>
      loadedLevel (bindingState (2 * r) 2
        (coalescedBindingP m r) (coalescedBindingQ m r)
        (bindingLinearPath (coalescedFiniteState (m + 1) r).S
          (coalescedInverseResponse m r q) t)) k) =
      (fun t : ℝ =>
        bindingLoadedLevel (2 * r) 2
          (coalescedBindingP m r) (coalescedBindingQ m r)
          (bindingLinearPath (coalescedFiniteState (m + 1) r).S
            (coalescedInverseResponse m r q) t) k) := by
    funext t
    exact coalescedBindingLevel_eq_loadedLevel m r _ k
  rw [hfun]
  exact h

/-- Zero-sum loaded forcing produces a tangent to the fixed literal
substrate-total class. -/
theorem coalescedBindingPath_totalS_eventually_hasDerivAt_zero (m : ℕ) :
    ∀ᶠ r : ℝ in atTop,
      ∀ (q : Fin (m + 3) → ℝ),
        (∑ k, q k) = 0 →
        HasDerivAt (fun t : ℝ =>
          totalS (bindingState (2 * r) 2
            (coalescedBindingP m r) (coalescedBindingQ m r)
            (bindingLinearPath (coalescedFiniteState (m + 1) r).S
              (coalescedInverseResponse m r q) t))) 0 0 := by
  filter_upwards [coalescedLiteralInventory_eventually_hasDerivAt m]
    with r hlevels
  intro q hq
  have hs : HasDerivAt (fun t : ℝ =>
      ∑ k : Fin (m + 3),
        loadedLevel (bindingState (2 * r) 2
          (coalescedBindingP m r) (coalescedBindingQ m r)
          (bindingLinearPath (coalescedFiniteState (m + 1) r).S
            (coalescedInverseResponse m r q) t)) k)
      (∑ k : Fin (m + 3), r * q k) 0 := by
    apply HasDerivAt.fun_sum
    intro k _
    exact hlevels q k
  have hfun : (fun t : ℝ =>
      ∑ k : Fin (m + 3),
        loadedLevel (bindingState (2 * r) 2
          (coalescedBindingP m r) (coalescedBindingQ m r)
          (bindingLinearPath (coalescedFiniteState (m + 1) r).S
            (coalescedInverseResponse m r q) t)) k) =
      (fun t : ℝ =>
        totalS (bindingState (2 * r) 2
          (coalescedBindingP m r) (coalescedBindingQ m r)
          (bindingLinearPath (coalescedFiniteState (m + 1) r).S
            (coalescedInverseResponse m r q) t))) := by
    funext t
    exact sum_loadedLevel_eq_totalS _
  have hzero : (∑ k : Fin (m + 3), r * q k) = 0 := by
    rw [← Finset.mul_sum, hq, mul_zero]
  rw [hfun, hzero] at hs
  exact hs

end
end PhosphorylationStableCapacity
