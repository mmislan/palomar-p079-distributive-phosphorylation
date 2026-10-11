module
public import proofs.PhosphorylationStableCapacity.LoadedJacobianFourBlocks

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section
open PhosphorylationSharpness

/-- The four named blocks reconstruct the entire literal loaded class
Fréchet derivative on every slow/fast perturbation. -/
theorem loadedFderiv_block_action {n : ℕ} (ET FT ST : ℝ)
    (k : Rates n) (u : CoordinateSpace n)
    (s : SlowSpace n) (f : FastSpace n) :
    fderiv ℝ (loadedRestrictedField ET FT ST k) u (s, f) =
      (loadedBlockA ET FT ST k u s + loadedBlockB ET FT ST k u f,
        loadedBlockC ET FT ST k u s + loadedBlockD ET FT ST k u f) := by
  let J := fderiv ℝ (loadedRestrictedField ET FT ST k) u
  have hsplit : ((s, f) : CoordinateSpace n) = (s, 0) + (0, f) := by
    simp
  change J (s, f) = _
  rw [hsplit, map_add]
  rfl

end
end PhosphorylationStableCapacity
