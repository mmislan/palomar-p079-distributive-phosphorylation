module
public import proofs.PhosphorylationStableCapacity.LoadedBindingRealization
public import proofs.PhosphorylationStableCapacity.CoalescedFiniteModeBlock

@[expose] public section

namespace PhosphorylationStableCapacity

open Filter PhosphorylationSharpness

noncomputable section

theorem coalescedFiniteCLevel_sum (m : ℕ) (r : ℝ) :
    (∑ i : Fin (m + 3), coalescedFiniteCLevel m r i) =
      ∑ i : Fin (m + 2), (coalescedFiniteState (m + 1) r).C i := by
  rw [Fin.sum_univ_castSucc]
  have hlast : coalescedFiniteCLevel m r (Fin.last (m + 2)) = 0 := by
    simp [coalescedFiniteCLevel, Fin.val_last]
  rw [hlast, add_zero]
  exact coalescedFiniteCLevel_occupied_sum m r

def coalescedBindingP (m : ℕ) (r : ℝ) (i : Fin (m + 3)) : ℝ :=
  coalescedFiniteCLevel m r i / (coalescedFiniteState (m + 1) r).S i

def coalescedBindingQ (m : ℕ) (r : ℝ) (i : Fin (m + 3)) : ℝ :=
  coalescedFiniteYLevel m r i / (coalescedFiniteState (m + 1) r).S i

/-- At the literal coalesced source equilibrium, the candidate loaded mass
matrix is the directional derivative of the reversible binding-equilibrium
level inventory. It has not yet been identified with the catalytic slow field. -/
theorem coalescedFullMass_hasDerivAt_bindingLevel
    (m : ℕ) (r : ℝ) (σ : Fin (m + 3) → ℝ) (i : Fin (m + 3))
    (hpos : (coalescedFiniteState (m + 1) r).Positive)
    (hC : (∑ j : Fin (m + 2),
      (coalescedFiniteState (m + 1) r).C j) = 2 * r - 1)
    (hD : (∑ j : Fin (m + 2),
      (coalescedFiniteState (m + 1) r).D j) = 1)
    (hr : r ≠ 0) :
    HasDerivAt (fun t : ℝ =>
      bindingLoadedLevel (2 * r) 2 (coalescedBindingP m r)
        (coalescedBindingQ m r)
        (bindingLinearPath (coalescedFiniteState (m + 1) r).S σ t) i)
      ((coalescedFullMass m r).mulVec σ i) 0 := by
  have hS : ∀ j : Fin (m + 3),
      (coalescedFiniteState (m + 1) r).S j ≠ 0 :=
    fun j => ne_of_gt (hpos.1 j)
  have hET : 2 * r = 1 + ∑ j : Fin (m + 3),
      coalescedFiniteCLevel m r j := by
    rw [coalescedFiniteCLevel_sum, hC]
    ring
  have hFT : (2 : ℝ) = 1 + ∑ j : Fin (m + 3),
      coalescedFiniteYLevel m r j := by
    rw [coalescedFiniteYLevel_sum, hD]
    ring
  have hET0 : 2 * r ≠ 0 := mul_ne_zero (by norm_num) hr
  have h := loadedBindingMass_hasDerivAt_from_concentrations
    (2 * r) 2 (coalescedFiniteState (m + 1) r).S
    (coalescedFiniteCLevel m r) (coalescedFiniteYLevel m r)
    σ i hS hET hFT hET0 (by norm_num)
  change HasDerivAt (fun t : ℝ =>
    bindingLoadedLevel (2 * r) 2
      (fun j => coalescedFiniteCLevel m r j /
        (coalescedFiniteState (m + 1) r).S j)
      (fun j => coalescedFiniteYLevel m r j /
        (coalescedFiniteState (m + 1) r).S j)
      (bindingLinearPath (coalescedFiniteState (m + 1) r).S σ t) i)
    ((coalescedFullMass m r).mulVec σ i) 0
  rw [coalescedFullMass_eq_loadedBindingMass]
  exact h

/-- The derivative identification applies at every sufficiently large
literal coalesced equilibrium, for every substrate tangent and level. -/
theorem coalescedFullMass_eventually_hasDerivAt_bindingLevel (m : ℕ) :
    ∀ᶠ r : ℝ in atTop, ∀ (σ : Fin (m + 3) → ℝ) (i : Fin (m + 3)),
      HasDerivAt (fun t : ℝ =>
        bindingLoadedLevel (2 * r) 2 (coalescedBindingP m r)
          (coalescedBindingQ m r)
          (bindingLinearPath (coalescedFiniteState (m + 1) r).S σ t) i)
        ((coalescedFullMass m r).mulVec σ i) 0 := by
  filter_upwards [coalescedFiniteState_eventually_equilibrium (m + 1),
    coalescedFiniteState_eventually_component_totals (m + 1),
    eventually_gt_atTop (0 : ℝ)] with r hstate htot hr
  intro σ i
  exact coalescedFullMass_hasDerivAt_bindingLevel m r σ i
    hstate.2.1 htot.1 htot.2.1 (ne_of_gt hr)

end
end PhosphorylationStableCapacity
