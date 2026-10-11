module
public import proofs.PhosphorylationStableCapacity.LoadedJacobianFourBlocks
public import proofs.PhosphorylationStableCapacity.LoadedFastBlockIdentification

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section
open PhosphorylationSharpness

/-- The lower-right block of the literal loaded class derivative, as a
linear map, is exactly the previously verified fast binding operator. -/
theorem loadedBlockD_toLinearMap_eq_fastBinding {n : ℕ}
    (ET FT ST : ℝ) (k : Rates n) (u : CoordinateSpace n)
    (hpos : (stateFromLoaded ET FT ST u).Positive)
    (heq : Equilibrium k (stateFromLoaded ET FT ST u)) :
    (loadedBlockD ET FT ST k u).toLinearMap =
      fastBindingEnd n (stateFromLoaded ET FT ST u)
        (fun j => k.a j * (stateFromLoaded ET FT ST u).S j.castSucc *
          (stateFromLoaded ET FT ST u).E)
        (fun j => k.alpha j * (stateFromLoaded ET FT ST u).S j.succ *
          (stateFromLoaded ET FT ST u).F) := by
  apply LinearMap.ext
  intro v
  simpa [loadedBlockD, fastEmbed, fastBindingEnd] using
    loadedFastBlock_eq_fastBinding ET FT ST k u v hpos heq

end
end PhosphorylationStableCapacity
