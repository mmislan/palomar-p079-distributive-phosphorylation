module
public import proofs.PhosphorylationStableCapacity.FastBindingQuadraticPathEquilibrium
public import Mathlib.Analysis.Calculus.LineDeriv.Basic

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section
open PhosphorylationSharpness

-- The function-equality branch is required by the newer mathlib pin.
set_option linter.unreachableTactic false in
set_option linter.unusedTactic false in
theorem hasDerivAt_quadratic_at_zero (b l q : ℝ) :
    HasDerivAt (fun t : ℝ => b + t * l + t ^ 2 * q) l 0 := by
  have h := ((hasDerivAt_const (0 : ℝ) b).add
    ((hasDerivAt_id (0 : ℝ)).mul_const l)).add
    (((hasDerivAt_id (0 : ℝ)).pow 2).mul_const q)
  convert h using 1
  all_goals
    first
    | funext t; simp only [Pi.add_apply, Pi.pow_apply, id_eq]
    | norm_num

/-- The literal phosphatase velocity has the abstract fast binding component
as its directional derivative at a positive equilibrium. -/
theorem loadedFastField_D_hasLineDerivAt {n : ℕ} (ET FT ST : ℝ)
    (k : Rates n) (u : CoordinateSpace n) (v : FastSpace n) (i : Fin n)
    (hpos : (stateFromLoaded ET FT ST u).Positive)
    (heq : Equilibrium k (stateFromLoaded ET FT ST u)) :
    HasLineDerivAt ℝ
      (fun w : CoordinateSpace n => (loadedRestrictedField ET FT ST k w).2.2 i)
      ((fastBindingLinear (stateFromLoaded ET FT ST u)
        (fun j => k.a j * (stateFromLoaded ET FT ST u).S j.castSucc *
          (stateFromLoaded ET FT ST u).E)
        (fun j => k.alpha j * (stateFromLoaded ET FT ST u).S j.succ *
          (stateFromLoaded ET FT ST u).F) v).2 i)
      u (fastEmbed v) := by
  let b := (loadedRestrictedField ET FT ST k u).2.2 i
  let l := (fastBindingLinear (stateFromLoaded ET FT ST u)
    (fun j => k.a j * (stateFromLoaded ET FT ST u).S j.castSucc *
      (stateFromLoaded ET FT ST u).E)
    (fun j => k.alpha j * (stateFromLoaded ET FT ST u).S j.succ *
      (stateFromLoaded ET FT ST u).F) v).2 i
  let q := k.alpha i * fastDeltaS v i.succ * fastDeltaF v
  have hp : (fun t : ℝ =>
      (loadedRestrictedField ET FT ST k (u + t • fastEmbed v)).2.2 i) =
      (fun t : ℝ => b + t * l + t ^ 2 * q) := by
    funext t
    exact loadedFastField_D_quadraticPath ET FT ST k u v i hpos heq t
  change HasDerivAt (fun t : ℝ =>
    (loadedRestrictedField ET FT ST k (u + t • fastEmbed v)).2.2 i) l 0
  rw [hp]
  exact hasDerivAt_quadratic_at_zero b l q

end
end PhosphorylationStableCapacity
