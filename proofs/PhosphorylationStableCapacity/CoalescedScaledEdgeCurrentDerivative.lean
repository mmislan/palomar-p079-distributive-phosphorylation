module
public import proofs.PhosphorylationStableCapacity.CoalescedScaledEdgeCurrentLimit

@[expose] public section

namespace PhosphorylationStableCapacity

open Filter PhosphorylationSharpness

noncomputable section

/-- The scaled first-prefix edge action is the literal catalytic-current
derivative along the actual scaled inverse-response tangent, eventually on
the coalesced source. -/
theorem coalescedScaledEdgeCurrent_eventually_hasDerivAt (m : ℕ)
    (q : Fin (m + 3) → ℝ) :
    ∀ᶠ r : ℝ in atTop,
      ∀ i : Fin (m + 1),
        HasDerivAt (fun t : ℝ =>
          bindingCatalyticCurrent (2 * r) 2
            (coalescedBindingP m r) (coalescedBindingQ m r)
            Fin.castSucc Fin.succ
            (coalescedFiniteRates (m + 1) r).c
            (coalescedFiniteRates (m + 1) r).gamma
            (bindingLinearPath (coalescedFiniteState (m + 1) r).S
              (coalescedInverseResponse m r q) t) i.castSucc)
          (coalescedScaledEdgeCurrent m r q i) 0 := by
  filter_upwards [coalescedFiniteState_eventually_equilibrium (m + 1),
    coalescedFiniteState_eventually_component_totals (m + 1),
    eventually_gt_atTop (0 : ℝ)] with r hstate htot hr
  intro i
  have h := coalescedCatalyticCurrent_hasDerivAt_D_weight
    m r (coalescedInverseResponse m r q) i.castSucc
    hstate.2.1 htot.1 htot.2.1 (ne_of_gt hr)
  have hindex : (i.castSucc.succ : Fin (m + 3)) =
      i.succ.castSucc := by
    ext
    rfl
  rw [hindex] at h
  convert h using 1
  simp only [coalescedScaledEdgeCurrent,
    coalescedInverseFeedback_eq_current_form]
  ring

end
end PhosphorylationStableCapacity
