module
public import proofs.PhosphorylationStableCapacity.CoalescedArbitraryInventoryDerivative
public import proofs.PhosphorylationStableCapacity.CoalescedFullLoadedMatrix

@[expose] public section

namespace PhosphorylationStableCapacity

open Filter PhosphorylationSharpness

noncomputable section

/-- On every inverse-response direction, the derivative of each literal
binding-manifold catalytic current is the source's finite current matrix
applied to that direction. -/
theorem coalescedInverseCurrent_eventually_hasDerivAt (m : ℕ) :
    ∀ᶠ r : ℝ in atTop,
      ∀ (q : Fin (m + 3) → ℝ) (i : Fin (m + 2)),
        HasDerivAt (fun t : ℝ =>
          bindingCatalyticCurrent (2 * r) 2
            (coalescedBindingP m r) (coalescedBindingQ m r)
            Fin.castSucc Fin.succ
            (coalescedFiniteRates (m + 1) r).c
            (coalescedFiniteRates (m + 1) r).gamma
            (bindingLinearPath (coalescedFiniteState (m + 1) r).S
              (coalescedInverseResponse m r q) t) i)
          ((coalescedCurrentJacobianMatrix m r).mulVec
            (coalescedInverseResponse m r q) i) 0 := by
  filter_upwards [coalescedFiniteState_eventually_equilibrium (m + 1),
    coalescedFiniteState_eventually_component_totals (m + 1),
    eventually_gt_atTop (0 : ℝ)] with r hstate htot hr
  intro q i
  exact coalescedCatalyticCurrent_hasDerivAt_matrix m r
    (coalescedInverseResponse m r q) i
    hstate.2.1 htot.1 htot.2.1 (ne_of_gt hr)

/-- The preceding derivative is exactly the finite current response to
`r` times the inverse loaded-mass forcing. -/
theorem coalescedInverseCurrent_eventually_hasDerivAt_mass (m : ℕ) :
    ∀ᶠ r : ℝ in atTop,
      ∀ (q : Fin (m + 3) → ℝ) (i : Fin (m + 2)),
        HasDerivAt (fun t : ℝ =>
          bindingCatalyticCurrent (2 * r) 2
            (coalescedBindingP m r) (coalescedBindingQ m r)
            Fin.castSucc Fin.succ
            (coalescedFiniteRates (m + 1) r).c
            (coalescedFiniteRates (m + 1) r).gamma
            (bindingLinearPath (coalescedFiniteState (m + 1) r).S
              (coalescedInverseResponse m r q) t) i)
          (r * (coalescedCurrentJacobianMatrix m r).mulVec
            ((coalescedFullMass m r)⁻¹.mulVec q) i) 0 := by
  filter_upwards [coalescedInverseCurrent_eventually_hasDerivAt m]
    with r hcurrent
  intro q i
  have h := hcurrent q i
  change HasDerivAt _
    ((coalescedCurrentJacobianMatrix m r).mulVec
      (r • (coalescedFullMass m r)⁻¹.mulVec q) i) 0 at h
  rw [Matrix.mulVec_smul] at h
  simpa only [Pi.smul_apply, smul_eq_mul] using h

end
end PhosphorylationStableCapacity
