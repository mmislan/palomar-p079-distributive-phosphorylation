module
public import proofs.PhosphorylationStableCapacity.CoalescedPrefixEdgeForcing
public import proofs.PhosphorylationStableCapacity.CoalescedBindingDerivative

@[expose] public section

namespace PhosphorylationStableCapacity

open Filter PhosphorylationSharpness

noncomputable section

/-- Along the actual inverse-response tangent to a first-prefix edge
column, the loaded inventory derivative is exactly `r` times that column.
The zero-sum and final-zero properties of the column are proved separately
in `CoalescedPrefixEdgeForcing`. -/
theorem coalescedPrefixInventory_eventually_hasDerivAt (m : ℕ) :
    ∀ᶠ r : ℝ in atTop,
      ∀ (j : Fin (m + 1)) (k : Fin (m + 3)),
        HasDerivAt (fun t : ℝ =>
          bindingLoadedLevel (2 * r) 2
            (coalescedBindingP m r) (coalescedBindingQ m r)
            (bindingLinearPath (coalescedFiniteState (m + 1) r).S
              (coalescedInverseResponse m r
                (coalescedPrefixEdgeForcing m j)) t) k)
          (r * coalescedPrefixEdgeForcing m j k) 0 := by
  filter_upwards [coalescedFullMass_eventually_hasDerivAt_bindingLevel m,
    coalescedFullMass_eventually_det_ne_zero m] with r hmass hdet
  intro j k
  have h := hmass
    (coalescedInverseResponse m r (coalescedPrefixEdgeForcing m j)) k
  have heq :
      (coalescedFullMass m r).mulVec
        (coalescedInverseResponse m r (coalescedPrefixEdgeForcing m j)) k =
          r * coalescedPrefixEdgeForcing m j k := by
    have hs := congrArg (fun f : Fin (m + 3) → ℝ => f k)
      (coalescedInverseResponse_mass_equation m r
        (coalescedPrefixEdgeForcing m j) hdet)
    simpa only [Pi.smul_apply, smul_eq_mul] using hs
  rw [heq] at h
  exact h

end
end PhosphorylationStableCapacity
