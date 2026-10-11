module
public import proofs.PhosphorylationStableCapacity.CoalescedMassModeColumns

@[expose] public section

namespace PhosphorylationStableCapacity

open PhosphorylationSharpness

noncomputable section

/-- The occupied row replaced by the total inventory equation. -/
def coalescedModeRow (m : ℕ) : Fin (m + 3) := ⟨m + 1, by omega⟩

/-- A square system for the singular inverse response: retain the first
`m+1` scaled mass rows, then use the unscaled total row and final row. -/
def coalescedReplacementMass (m : ℕ) (r : ℝ) :
    Matrix (Fin (m + 3)) (Fin (m + 3)) ℝ :=
  fun i j =>
    if i.val < m + 1 then coalescedFullMass m r i j / r
    else if i.val = m + 1 then
      ∑ k : Fin (m + 3), coalescedFullMass m r k j
    else coalescedFullMass m r i j

theorem coalescedReplacementMass_prefix_row
    (m : ℕ) (r : ℝ) (i : Fin (m + 1)) (j : Fin (m + 3)) :
    coalescedReplacementMass m r i.castSucc.castSucc j =
      coalescedFullMass m r i.castSucc.castSucc j / r := by
  simp [coalescedReplacementMass, i.isLt]

theorem coalescedReplacementMass_mode_row
    (m : ℕ) (r : ℝ) (j : Fin (m + 3)) :
    coalescedReplacementMass m r (coalescedModeRow m) j =
      ∑ k : Fin (m + 3), coalescedFullMass m r k j := by
  simp [coalescedReplacementMass, coalescedModeRow]

theorem coalescedReplacementMass_final_row
    (m : ℕ) (r : ℝ) (j : Fin (m + 3)) :
    coalescedReplacementMass m r (Fin.last (m + 2)) j =
      coalescedFullMass m r (Fin.last (m + 2)) j := by
  simp [coalescedReplacementMass, Fin.val_last]

/-- The replacement total row is a literal finite concentration formula,
given the exact source enzyme totals. -/
theorem coalescedReplacementMass_mode_row_formula
    (m : ℕ) (r : ℝ) (j : Fin (m + 3))
    (hr : r ≠ 0)
    (hC : (∑ i : Fin (m + 2),
      (coalescedFiniteState (m + 1) r).C i) = 2 * r - 1)
    (hD : (∑ i : Fin (m + 2),
      (coalescedFiniteState (m + 1) r).D i) = 1) :
    coalescedReplacementMass m r (coalescedModeRow m) j =
      (coalescedFiniteState (m + 1) r).S j +
        coalescedFiniteCLevel m r j / (2 * r) +
          coalescedFiniteYLevel m r j / 2 := by
  rw [coalescedReplacementMass_mode_row]
  exact coalescedFullMass_column_sum m r j hr hC hD

/-- The replacement final row is likewise explicit at every parameter. -/
theorem coalescedReplacementMass_final_row_formula
    (m : ℕ) (r : ℝ) (j : Fin (m + 3)) :
    coalescedReplacementMass m r (Fin.last (m + 2)) j =
      (if Fin.last (m + 2) = j then
        2 * coalescedFiniteYLevel m r (Fin.last (m + 2)) else 0) -
        coalescedFiniteYLevel m r (Fin.last (m + 2)) *
          coalescedFiniteYLevel m r j / 2 := by
  rw [coalescedReplacementMass_final_row]
  exact coalescedFullMass_final_row m r j

end
end PhosphorylationStableCapacity
