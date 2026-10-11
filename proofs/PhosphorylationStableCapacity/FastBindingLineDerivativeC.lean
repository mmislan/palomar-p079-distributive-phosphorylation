module
public import proofs.PhosphorylationStableCapacity.FastBindingLineDerivativeD

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section
open PhosphorylationSharpness

/-- The literal kinase velocity has the abstract fast binding component
as its directional derivative at a positive equilibrium. -/
theorem loadedFastField_C_hasLineDerivAt {n : ℕ} (ET FT ST : ℝ)
    (k : Rates n) (u : CoordinateSpace n) (v : FastSpace n) (i : Fin n)
    (hpos : (stateFromLoaded ET FT ST u).Positive)
    (heq : Equilibrium k (stateFromLoaded ET FT ST u)) :
    HasLineDerivAt ℝ
      (fun w : CoordinateSpace n => (loadedRestrictedField ET FT ST k w).2.1 i)
      ((fastBindingLinear (stateFromLoaded ET FT ST u)
        (fun j => k.a j * (stateFromLoaded ET FT ST u).S j.castSucc *
          (stateFromLoaded ET FT ST u).E)
        (fun j => k.alpha j * (stateFromLoaded ET FT ST u).S j.succ *
          (stateFromLoaded ET FT ST u).F) v).1 i)
      u (fastEmbed v) := by
  let b := (loadedRestrictedField ET FT ST k u).2.1 i
  let l := -(k.a i * (stateFromLoaded ET FT ST u).S i.castSucc *
      (stateFromLoaded ET FT ST u).E) *
      fastAffinityC (stateFromLoaded ET FT ST u) v i
  let q := k.a i * fastDeltaS v i.castSucc * fastDeltaE v
  have hp : (fun t : ℝ =>
      (loadedRestrictedField ET FT ST k (u + t • fastEmbed v)).2.1 i) =
      (fun t : ℝ => b + t * l + t ^ 2 * q) := by
    funext t
    exact loadedFastField_C_quadraticPath ET FT ST k u v i hpos heq t
  change HasDerivAt (fun t : ℝ =>
    (loadedRestrictedField ET FT ST k (u + t • fastEmbed v)).2.1 i) l 0
  rw [hp]
  exact hasDerivAt_quadratic_at_zero b l q

end
end PhosphorylationStableCapacity
