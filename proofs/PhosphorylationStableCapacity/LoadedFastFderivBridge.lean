module
public import proofs.PhosphorylationStableCapacity.FastBindingLineDerivativeC
public import proofs.PhosphorylationStableCapacity.LoadedFieldDifferentiability

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section
open PhosphorylationSharpness

/-- The phosphatase rows of the literal loaded Fréchet derivative, restricted
to fast-coordinate perturbations, equal the abstract fast binding operator. -/
theorem loadedFastFderiv_D_eq_fastBinding {n : ℕ} (ET FT ST : ℝ)
    (k : Rates n) (u : CoordinateSpace n) (v : FastSpace n) (i : Fin n)
    (hpos : (stateFromLoaded ET FT ST u).Positive)
    (heq : Equilibrium k (stateFromLoaded ET FT ST u)) :
    (fderiv ℝ (loadedRestrictedField ET FT ST k) u (fastEmbed v)).2.2 i =
      (fastBindingLinear (stateFromLoaded ET FT ST u)
        (fun j => k.a j * (stateFromLoaded ET FT ST u).S j.castSucc *
          (stateFromLoaded ET FT ST u).E)
        (fun j => k.alpha j * (stateFromLoaded ET FT ST u).S j.succ *
          (stateFromLoaded ET FT ST u).F) v).2 i := by
  have hf := ((differentiable_loadedRestrictedField ET FT ST k).differentiableAt
    (x := u)).hasFDerivAt
  have hcomponent := (hasFDerivAt_pi'.mp (hf.snd.snd)) i
  have hline := hcomponent.hasLineDerivAt (fastEmbed v)
  have hknown := loadedFastField_D_hasLineDerivAt ET FT ST k u v i hpos heq
  simpa using hline.unique hknown

/-- The kinase rows of the literal loaded Fréchet derivative have the same
fast binding operator. -/
theorem loadedFastFderiv_C_eq_fastBinding {n : ℕ} (ET FT ST : ℝ)
    (k : Rates n) (u : CoordinateSpace n) (v : FastSpace n) (i : Fin n)
    (hpos : (stateFromLoaded ET FT ST u).Positive)
    (heq : Equilibrium k (stateFromLoaded ET FT ST u)) :
    (fderiv ℝ (loadedRestrictedField ET FT ST k) u (fastEmbed v)).2.1 i =
      (fastBindingLinear (stateFromLoaded ET FT ST u)
        (fun j => k.a j * (stateFromLoaded ET FT ST u).S j.castSucc *
          (stateFromLoaded ET FT ST u).E)
        (fun j => k.alpha j * (stateFromLoaded ET FT ST u).S j.succ *
          (stateFromLoaded ET FT ST u).F) v).1 i := by
  have hf := ((differentiable_loadedRestrictedField ET FT ST k).differentiableAt
    (x := u)).hasFDerivAt
  have hcomponent := (hasFDerivAt_pi'.mp (hf.snd.fst)) i
  have hline := hcomponent.hasLineDerivAt (fastEmbed v)
  have hknown := loadedFastField_C_hasLineDerivAt ET FT ST k u v i hpos heq
  simpa using hline.unique hknown

end
end PhosphorylationStableCapacity
