module
public import proofs.PhosphorylationStableCapacity.LoadedBindingModeRows
public import proofs.PhosphorylationStableCapacity.CoalescedBindingDerivative

@[expose] public section

namespace PhosphorylationStableCapacity

open Filter PhosphorylationSharpness

noncomputable section

/-- At a literal coalesced state with its exact enzyme totals, the sum of
the finite loaded-mass rows is the free-substrate response plus the two
free-enzyme shares of complex response. -/
theorem coalescedFullMass_total_action
    (m : ℕ) (r : ℝ) (σ : Fin (m + 3) → ℝ)
    (hr : r ≠ 0)
    (hC : (∑ i : Fin (m + 2),
      (coalescedFiniteState (m + 1) r).C i) = 2 * r - 1)
    (hD : (∑ i : Fin (m + 2),
      (coalescedFiniteState (m + 1) r).D i) = 1) :
    (∑ i : Fin (m + 3), (coalescedFullMass m r).mulVec σ i) =
      (∑ i : Fin (m + 3),
        (coalescedFiniteState (m + 1) r).S i * σ i) +
        (∑ i : Fin (m + 3), coalescedFiniteCLevel m r i * σ i) /
          (2 * r) +
          (∑ i : Fin (m + 3), coalescedFiniteYLevel m r i * σ i) / 2 := by
  have hET : 2 * r = 1 + ∑ i : Fin (m + 3),
      coalescedFiniteCLevel m r i := by
    rw [coalescedFiniteCLevel_sum, hC]
    ring
  have hFT : (2 : ℝ) = 1 + ∑ i : Fin (m + 3),
      coalescedFiniteYLevel m r i := by
    rw [coalescedFiniteYLevel_sum, hD]
    ring
  rw [coalescedFullMass_eq_loadedBindingMass]
  exact loadedBindingMass_total_action _ _ _ σ (2 * r) 2
    hET hFT (mul_ne_zero (by norm_num) hr) (by norm_num)

/-- A zero final row of the finite loaded mass equation fixes the final
log-substrate response by the phosphatase-weighted response, exactly at
every positive literal coalesced state. -/
theorem coalescedFullMass_final_zero_equation
    (m : ℕ) (r : ℝ) (σ : Fin (m + 3) → ℝ)
    (hpos : (coalescedFiniteState (m + 1) r).Positive)
    (hzero : (coalescedFullMass m r).mulVec σ
      (Fin.last (m + 2)) = 0) :
    (∑ i : Fin (m + 3), coalescedFiniteYLevel m r i * σ i) =
      4 * σ (Fin.last (m + 2)) := by
  have hC : coalescedFiniteCLevel m r (Fin.last (m + 2)) = 0 := by
    simp [coalescedFiniteCLevel, Fin.val_last]
  have hS : (coalescedFiniteState (m + 1) r).S
      (Fin.last (m + 2)) =
        coalescedFiniteYLevel m r (Fin.last (m + 2)) := by
    rw [coalescedFiniteYLevel_last,
      coalescedFiniteState_lastS_eq_lastD]
  have hY : coalescedFiniteYLevel m r (Fin.last (m + 2)) ≠ 0 := by
    rw [coalescedFiniteYLevel_last]
    exact ne_of_gt (hpos.2.2.2.2 (Fin.last (m + 1)))
  rw [coalescedFullMass_eq_loadedBindingMass] at hzero
  exact loadedBindingMass_final_zero_equation
    (coalescedFiniteState (m + 1) r).S
    (coalescedFiniteCLevel m r) (coalescedFiniteYLevel m r)
    σ (2 * r) (Fin.last (m + 2)) hC hS hY hzero

/-- The final-row identity applies uniformly at every sufficiently large
parameter of the literal coalesced source. -/
theorem coalescedFullMass_eventually_final_zero_equation (m : ℕ) :
    ∀ᶠ r : ℝ in atTop, ∀ σ : Fin (m + 3) → ℝ,
      (coalescedFullMass m r).mulVec σ (Fin.last (m + 2)) = 0 →
        (∑ i : Fin (m + 3), coalescedFiniteYLevel m r i * σ i) =
          4 * σ (Fin.last (m + 2)) := by
  filter_upwards [coalescedFiniteState_eventually_equilibrium (m + 1)]
    with r hr σ hzero
  exact coalescedFullMass_final_zero_equation m r σ hr.2.1 hzero

end
end PhosphorylationStableCapacity
