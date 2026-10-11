module
public import proofs.PhosphorylationStableCapacity.ArbitrarySplitPair

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section

/-- Strictly ordered offsets have a nonzero derivative root-gap at every
    selected root, independently of its parity. -/
theorem arbitrarySplit_root_gap_ne_zero
    (m : ℕ) (ξ : ℕ → ℝ) (hξ : StrictMono ξ)
    (j : Fin (2*m+1)) :
    (∏ i ∈ (Finset.range (2*m+1)).erase j.val,
      (ξ j.val-ξ i)) ≠ 0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro i hi
  have hij : i ≠ j.val := (Finset.mem_erase.mp hi).1
  apply sub_ne_zero.mpr
  intro heq
  exact hij (hξ.injective heq).symm

end
end PhosphorylationStableCapacity
