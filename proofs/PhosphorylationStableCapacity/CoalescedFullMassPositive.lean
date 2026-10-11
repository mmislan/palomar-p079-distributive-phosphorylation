module
public import proofs.PhosphorylationStableCapacity.LoadedBindingPositive
public import proofs.PhosphorylationStableCapacity.CoalescedBindingDerivative

@[expose] public section

namespace PhosphorylationStableCapacity

open Filter PhosphorylationSharpness

noncomputable section

/-- The literal finite-parameter loaded mass matrix is nonsingular at every
positive coalesced source state satisfying its exact enzyme totals. -/
theorem coalescedFullMass_det_ne_zero
    (m : ℕ) (r : ℝ)
    (hpos : (coalescedFiniteState (m + 1) r).Positive)
    (hC : (∑ i : Fin (m + 2),
      (coalescedFiniteState (m + 1) r).C i) = 2 * r - 1)
    (hD : (∑ i : Fin (m + 2),
      (coalescedFiniteState (m + 1) r).D i) = 1) :
    (coalescedFullMass m r).det ≠ 0 := by
  have hS : ∀ j : Fin (m + 3),
      0 < (coalescedFiniteState (m + 1) r).S j := hpos.1
  have hCnon : ∀ j : Fin (m + 3),
      0 ≤ coalescedFiniteCLevel m r j := by
    intro j
    unfold coalescedFiniteCLevel
    split_ifs
    · exact (hpos.2.2.2.1 _).le
    · exact le_refl 0
  have hYnon : ∀ j : Fin (m + 3),
      0 ≤ coalescedFiniteYLevel m r j := by
    intro j
    unfold coalescedFiniteYLevel
    split_ifs
    · exact le_refl 0
    · exact (hpos.2.2.2.2 _).le
  have hET : 2 * r = 1 + ∑ j : Fin (m + 3),
      coalescedFiniteCLevel m r j := by
    rw [coalescedFiniteCLevel_sum, hC]
    ring
  have hFT : (2 : ℝ) = 1 + ∑ j : Fin (m + 3),
      coalescedFiniteYLevel m r j := by
    rw [coalescedFiniteYLevel_sum, hD]
    ring
  rw [coalescedFullMass_eq_loadedBindingMass]
  exact loadedBindingMass_det_ne_zero
    (coalescedFiniteState (m + 1) r).S
    (coalescedFiniteCLevel m r) (coalescedFiniteYLevel m r)
    (2 * r) 2 hS hCnon hYnon hET hFT

/-- The full loaded mass matrix is nonsingular at every sufficiently large
literal coalesced source parameter. -/
theorem coalescedFullMass_eventually_det_ne_zero (m : ℕ) :
    ∀ᶠ r : ℝ in atTop, (coalescedFullMass m r).det ≠ 0 := by
  filter_upwards [coalescedFiniteState_eventually_equilibrium (m + 1),
    coalescedFiniteState_eventually_component_totals (m + 1)]
    with r hstate htot
  exact coalescedFullMass_det_ne_zero m r hstate.2.1 htot.1 htot.2.1

end
end PhosphorylationStableCapacity
