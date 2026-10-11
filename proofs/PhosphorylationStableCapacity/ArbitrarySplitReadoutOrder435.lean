module
public import proofs.PhosphorylationStableCapacity.ReadoutGlobalMonotonicity435

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section

open PhosphorylationSharpness Polynomial

/-- The literal physical readouts at ordered positive split roots inherit
the global scalar readout monotonicity with the same conversion polynomial. -/
theorem arbitrarySplitReadout_strictMono_all_roots
    (m : ℕ) (ξ : ℕ → ℝ) (r δ : ℝ)
    (hξ : StrictMono ξ) (hδ : 0 < δ)
    (hroot : ∀ i, i ≤ 2*m → 1 < offsetSplitRoot ξ δ i)
    (hD : DensePositive (arbitrarySplitRawD m ξ r δ) m) :
    StrictMono (fun j : Fin (2*m+1) =>
      fullyPhosphorylatedReadout m (arbitrarySplitFiniteState m ξ r δ j)) := by
  intro j k hjk
  have hj : 1 < offsetSplitRoot ξ δ j.val := hroot j.val (by omega)
  have hk : 1 < offsetSplitRoot ξ δ k.val := hroot k.val (by omega)
  change fullyPhosphorylatedReadout m (arbitrarySplitFiniteState m ξ r δ j) <
    fullyPhosphorylatedReadout m (arbitrarySplitFiniteState m ξ r δ k)
  rw [arbitrarySplitReadout_closed_form m ξ r δ hD j hj,
    arbitrarySplitReadout_closed_form m ξ r δ hD k hk]
  change splitReadoutScalar m (arbitrarySplitRawD m ξ r δ)
      (offsetSplitRoot ξ δ j.val) <
    splitReadoutScalar m (arbitrarySplitRawD m ξ r δ)
      (offsetSplitRoot ξ δ k.val)
  apply splitReadoutScalar_strictMonoOn_Ioi_one m _ hD hj hk
  unfold offsetSplitRoot
  exact add_lt_add_right (mul_lt_mul_of_pos_left (hξ hjk) hδ) 3

end

end PhosphorylationStableCapacity
