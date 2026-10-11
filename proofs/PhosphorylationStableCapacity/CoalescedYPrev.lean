module
public import proofs.PhosphorylationStableCapacity.CoalescedPathMean

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section

/-- The coalesced phosphatase weight at a level, with zero at level zero. -/
def coalescedYPrev (m i : ℕ) : ℝ :=
  if i = 0 then 0 else coalescedYNext m (i - 1)

theorem coalescedYPrev_centered_moment_range (m : ℕ) :
    (∑ i ∈ Finset.range (m + 2),
      coalescedYPrev m i * ((i : ℝ) - coalescedMu m)) =
        4 / 3 - coalescedV m * (((m : ℝ) + 2) - coalescedMu m) := by
  calc
    (∑ i ∈ Finset.range (m + 2),
      coalescedYPrev m i * ((i : ℝ) - coalescedMu m)) =
        ∑ i ∈ Finset.range (m + 1),
          coalescedYNext m i * (((i : ℝ) + 1) - coalescedMu m) := by
        have hindex : m + 2 = (m + 1) + 1 := by omega
        rw [hindex, Finset.sum_range_succ']
        simp [coalescedYPrev, Nat.cast_add]
    _ = _ := coalescedYPrev_centered_moment m

end
end PhosphorylationStableCapacity
