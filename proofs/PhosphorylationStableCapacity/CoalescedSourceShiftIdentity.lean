module
public import proofs.PhosphorylationStableCapacity.CoalescedReplacementInverseLimit

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section

/-- On each occupied level the literal limiting substrate concentration is
the sum of the adjacent phosphatase-complex weights. -/
theorem coalescedSubstrateLimit_adjacent_y (m : ℕ)
    (j : Fin (m + 2)) :
    coalescedSubstrateLimit (m + 1) j.val =
      coalescedFullYLimit m j.castSucc + coalescedYNext m j.val := by
  unfold coalescedSubstrateLimit coalescedFullYLimit coalescedYNext
  by_cases hj : j.val = 0
  · simp [hj]
  · simp [hj, add_div]
    ring

end
end PhosphorylationStableCapacity
