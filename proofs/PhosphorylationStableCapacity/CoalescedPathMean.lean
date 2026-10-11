module
public import proofs.PhosphorylationStableCapacity.CoalescedShiftedY
public import proofs.PhosphorylationStableCapacity.PathGain

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section

/-- The generic path center agrees with the normalized repeated-root source
center for every positive source length. -/
theorem coalescedPathMean (m : ℕ) :
    pathMean (m + 1) (coalescedLevelWeight m) = coalescedMu m := by
  unfold pathMean
  have hindex : m + 1 + 1 = m + 2 := by omega
  rw [hindex, coalescedLevelWeight_first_moment,
    coalescedLevelWeight_mass]
  unfold coalescedMu
  ring

end
end PhosphorylationStableCapacity
