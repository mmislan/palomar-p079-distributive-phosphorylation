module
public import proofs.PhosphorylationStableCapacity.FastBindingQuadraticPath
public import proofs.PhosphorylationStableCapacity.FastBindingRawCoefficient

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section
open PhosphorylationSharpness

/-- At a positive equilibrium, the phosphatase-complex path has the abstract
fast binding operator as its exact linear coefficient. -/
theorem loadedFastField_D_quadraticPath {n : ℕ} (ET FT ST : ℝ)
    (k : Rates n) (u : CoordinateSpace n) (v : FastSpace n) (i : Fin n)
    (hpos : (stateFromLoaded ET FT ST u).Positive)
    (heq : Equilibrium k (stateFromLoaded ET FT ST u)) (t : ℝ) :
    (loadedRestrictedField ET FT ST k (u + t • fastEmbed v)).2.2 i =
      (loadedRestrictedField ET FT ST k u).2.2 i +
      t * (fastBindingLinear (stateFromLoaded ET FT ST u)
        (fun j => k.a j * (stateFromLoaded ET FT ST u).S j.castSucc *
          (stateFromLoaded ET FT ST u).E)
        (fun j => k.alpha j * (stateFromLoaded ET FT ST u).S j.succ *
          (stateFromLoaded ET FT ST u).F) v).2 i +
      t ^ 2 * (k.alpha i * fastDeltaS v i.succ * fastDeltaF v) := by
  rw [loadedFastField_D_quadraticPath_raw ET FT ST k u v i t]
  rw [loadedFastField_D_rawCoefficient_eq_fastBinding ET FT ST k u v i
    hpos heq]

end
end PhosphorylationStableCapacity
