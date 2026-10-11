module
public import proofs.PhosphorylationStableCapacity.FastBindingQuadraticPathD

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section
open PhosphorylationSharpness

/-- The linear coefficient in the raw phosphatase quadratic path is exactly
the abstract fast binding operator at a positive equilibrium. -/
theorem loadedFastField_D_rawCoefficient_eq_fastBinding {n : ℕ}
    (ET FT ST : ℝ) (k : Rates n) (u : CoordinateSpace n)
    (v : FastSpace n) (i : Fin n)
    (hpos : (stateFromLoaded ET FT ST u).Positive)
    (heq : Equilibrium k (stateFromLoaded ET FT ST u)) :
    k.alpha i *
        ((stateFromLoaded ET FT ST u).S i.succ * fastDeltaF v +
          (stateFromLoaded ET FT ST u).F * fastDeltaS v i.succ) -
      (k.beta i + k.gamma i) * v.2 i =
      (fastBindingLinear (stateFromLoaded ET FT ST u)
        (fun j => k.a j * (stateFromLoaded ET FT ST u).S j.castSucc *
          (stateFromLoaded ET FT ST u).E)
        (fun j => k.alpha j * (stateFromLoaded ET FT ST u).S j.succ *
          (stateFromLoaded ET FT ST u).F) v).2 i := by
  have h := loadedFastField_difference_D_fastBinding ET FT ST k u v i
    hpos heq
  rw [loadedFastField_difference_D ET FT ST k u v i] at h
  linear_combination h

end
end PhosphorylationStableCapacity
