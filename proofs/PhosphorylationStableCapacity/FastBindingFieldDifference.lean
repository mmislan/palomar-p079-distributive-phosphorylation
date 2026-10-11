module
public import proofs.PhosphorylationStableCapacity.FastBindingStatePerturbation

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section
open PhosphorylationSharpness

/-- Exact finite complex-field difference under a fixed-loaded-level fast
perturbation, retaining its quadratic remainder. -/
theorem loadedFastField_difference_C {n : ℕ} (ET FT ST : ℝ)
    (k : Rates n) (u : CoordinateSpace n) (v : FastSpace n) (i : Fin n) :
    (loadedRestrictedField ET FT ST k (u + fastEmbed v)).2.1 i -
      (loadedRestrictedField ET FT ST k u).2.1 i =
      k.a i *
        ((stateFromLoaded ET FT ST u).S i.castSucc * fastDeltaE v +
          (stateFromLoaded ET FT ST u).E * fastDeltaS v i.castSucc +
          fastDeltaS v i.castSucc * fastDeltaE v) -
        (k.b i + k.c i) * v.1 i := by
  rw [loadedFastField_C, loadedFastField_C,
    stateFromLoaded_fast_S, stateFromLoaded_fast_E,
    stateFromLoaded_fast_C]
  ring

theorem loadedFastField_difference_D {n : ℕ} (ET FT ST : ℝ)
    (k : Rates n) (u : CoordinateSpace n) (v : FastSpace n) (i : Fin n) :
    (loadedRestrictedField ET FT ST k (u + fastEmbed v)).2.2 i -
      (loadedRestrictedField ET FT ST k u).2.2 i =
      k.alpha i *
        ((stateFromLoaded ET FT ST u).S i.succ * fastDeltaF v +
          (stateFromLoaded ET FT ST u).F * fastDeltaS v i.succ +
          fastDeltaS v i.succ * fastDeltaF v) -
        (k.beta i + k.gamma i) * v.2 i := by
  rw [loadedFastField_D, loadedFastField_D,
    stateFromLoaded_fast_S, stateFromLoaded_fast_F,
    stateFromLoaded_fast_D]
  ring

end
end PhosphorylationStableCapacity
