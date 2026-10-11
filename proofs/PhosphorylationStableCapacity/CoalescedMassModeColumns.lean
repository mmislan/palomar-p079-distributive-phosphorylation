module
public import proofs.PhosphorylationStableCapacity.LoadedBindingModeColumns
public import proofs.PhosphorylationStableCapacity.CoalescedBindingDerivative

@[expose] public section

namespace PhosphorylationStableCapacity

open PhosphorylationSharpness

noncomputable section

/-- The sum of the literal loaded-mass column is an exact finite-parameter
coefficient of the total-inventory mode row. -/
theorem coalescedFullMass_column_sum
    (m : ℕ) (r : ℝ) (j : Fin (m + 3))
    (hr : r ≠ 0)
    (hC : (∑ i : Fin (m + 2),
      (coalescedFiniteState (m + 1) r).C i) = 2 * r - 1)
    (hD : (∑ i : Fin (m + 2),
      (coalescedFiniteState (m + 1) r).D i) = 1) :
    (∑ i : Fin (m + 3), coalescedFullMass m r i j) =
      (coalescedFiniteState (m + 1) r).S j +
        coalescedFiniteCLevel m r j / (2 * r) +
          coalescedFiniteYLevel m r j / 2 := by
  have hET : 2 * r = 1 + ∑ i : Fin (m + 3),
      coalescedFiniteCLevel m r i := by
    rw [coalescedFiniteCLevel_sum, hC]
    ring
  have hFT : (2 : ℝ) = 1 + ∑ i : Fin (m + 3),
      coalescedFiniteYLevel m r i := by
    rw [coalescedFiniteYLevel_sum, hD]
    ring
  rw [coalescedFullMass_eq_loadedBindingMass]
  exact loadedBindingMass_column_sum
    (coalescedFiniteState (m + 1) r).S
    (coalescedFiniteCLevel m r) (coalescedFiniteYLevel m r)
    (2 * r) 2 hET hFT (mul_ne_zero (by norm_num) hr)
    (by norm_num) j

/-- The final literal mass row uses the exact equality of the final free
substrate and final phosphatase complex, with no kinase complex there. -/
theorem coalescedFullMass_final_row
    (m : ℕ) (r : ℝ) (j : Fin (m + 3)) :
    coalescedFullMass m r (Fin.last (m + 2)) j =
      (if Fin.last (m + 2) = j then
        2 * coalescedFiniteYLevel m r (Fin.last (m + 2)) else 0) -
        coalescedFiniteYLevel m r (Fin.last (m + 2)) *
          coalescedFiniteYLevel m r j / 2 := by
  have hC : coalescedFiniteCLevel m r (Fin.last (m + 2)) = 0 := by
    simp [coalescedFiniteCLevel, Fin.val_last]
  have hS : (coalescedFiniteState (m + 1) r).S
      (Fin.last (m + 2)) =
        coalescedFiniteYLevel m r (Fin.last (m + 2)) := by
    rw [coalescedFiniteYLevel_last,
      coalescedFiniteState_lastS_eq_lastD]
  simp [coalescedFullMass, hC, hS]
  ring_nf

end
end PhosphorylationStableCapacity
