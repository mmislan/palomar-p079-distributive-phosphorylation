module
public import proofs.PhosphorylationStableCapacity.LoadedFastFderivBridge

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section
open PhosphorylationSharpness

/-- The fast-fast block of the literal loaded compatibility-class Jacobian
is exactly the abstract fast binding operator at a positive equilibrium. -/
theorem loadedFastBlock_eq_fastBinding {n : ℕ} (ET FT ST : ℝ)
    (k : Rates n) (u : CoordinateSpace n) (v : FastSpace n)
    (hpos : (stateFromLoaded ET FT ST u).Positive)
    (heq : Equilibrium k (stateFromLoaded ET FT ST u)) :
    (fderiv ℝ (loadedRestrictedField ET FT ST k) u (fastEmbed v)).2 =
      fastBindingLinear (stateFromLoaded ET FT ST u)
        (fun j => k.a j * (stateFromLoaded ET FT ST u).S j.castSucc *
          (stateFromLoaded ET FT ST u).E)
        (fun j => k.alpha j * (stateFromLoaded ET FT ST u).S j.succ *
          (stateFromLoaded ET FT ST u).F) v := by
  apply Prod.ext
  · funext i
    exact loadedFastFderiv_C_eq_fastBinding ET FT ST k u v i hpos heq
  · funext i
    exact loadedFastFderiv_D_eq_fastBinding ET FT ST k u v i hpos heq

end
end PhosphorylationStableCapacity
