module
public import proofs.PhosphorylationStableCapacity.LoadedBindingLevelBridge
public import proofs.PhosphorylationStableCapacity.CoalescedPrefixInventoryDerivative

@[expose] public section

namespace PhosphorylationStableCapacity

open Filter PhosphorylationSharpness

noncomputable section

/-- The source binding ratios have no kinase complex at the final level
and no phosphatase complex at level zero. -/
theorem coalescedBinding_endpoint_complexes_zero (m : ℕ) (r : ℝ)
    (S : Fin (m + 3) → ℝ) :
    bindingComplex (2 * r) (coalescedBindingP m r) S
        (Fin.last (m + 2)) = 0 ∧
      bindingComplex 2 (coalescedBindingQ m r) S 0 = 0 := by
  constructor
  · simp [bindingComplex, coalescedBindingP,
      coalescedFiniteCLevel, Fin.val_last]
  · simp [bindingComplex, coalescedBindingQ,
      coalescedFiniteYLevel]

/-- At every substrate state, the source's binding-level inventory is
the literal loaded-level coordinate of its binding state. -/
theorem coalescedBindingLevel_eq_loadedLevel (m : ℕ) (r : ℝ)
    (S : Fin (m + 3) → ℝ) (k : Fin (m + 3)) :
    loadedLevel (bindingState (2 * r) 2
      (coalescedBindingP m r) (coalescedBindingQ m r) S) k =
        bindingLoadedLevel (2 * r) 2
          (coalescedBindingP m r) (coalescedBindingQ m r) S k := by
  obtain ⟨hp, hq⟩ := coalescedBinding_endpoint_complexes_zero m r S
  exact loadedLevel_bindingState_eq_bindingLoadedLevel
    (2 * r) 2 (coalescedBindingP m r) (coalescedBindingQ m r)
    S hp hq k

/-- Each inverse-response edge column changes the literal loaded levels
by precisely `r` times its zero-sum incidence-transpose column. -/
theorem coalescedLiteralPrefixInventory_eventually_hasDerivAt (m : ℕ) :
    ∀ᶠ r : ℝ in atTop,
      ∀ (j : Fin (m + 1)) (k : Fin (m + 3)),
        HasDerivAt (fun t : ℝ =>
          loadedLevel (bindingState (2 * r) 2
            (coalescedBindingP m r) (coalescedBindingQ m r)
            (bindingLinearPath (coalescedFiniteState (m + 1) r).S
              (coalescedInverseResponse m r
                (coalescedPrefixEdgeForcing m j)) t)) k)
          (r * coalescedPrefixEdgeForcing m j k) 0 := by
  filter_upwards [coalescedPrefixInventory_eventually_hasDerivAt m]
    with r hmass
  intro j k
  have h := hmass j k
  have hfun : (fun t : ℝ =>
      loadedLevel (bindingState (2 * r) 2
        (coalescedBindingP m r) (coalescedBindingQ m r)
        (bindingLinearPath (coalescedFiniteState (m + 1) r).S
          (coalescedInverseResponse m r
            (coalescedPrefixEdgeForcing m j)) t)) k) =
      (fun t : ℝ =>
        bindingLoadedLevel (2 * r) 2
          (coalescedBindingP m r) (coalescedBindingQ m r)
          (bindingLinearPath (coalescedFiniteState (m + 1) r).S
            (coalescedInverseResponse m r
              (coalescedPrefixEdgeForcing m j)) t) k) := by
    funext t
    exact coalescedBindingLevel_eq_loadedLevel m r _ k
  rw [hfun]
  exact h

end
end PhosphorylationStableCapacity
