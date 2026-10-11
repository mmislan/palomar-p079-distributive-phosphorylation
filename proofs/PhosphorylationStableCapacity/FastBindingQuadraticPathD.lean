module
public import proofs.PhosphorylationStableCapacity.FastBindingScaling

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section
open PhosphorylationSharpness

/-- The phosphatase-complex velocity is a quadratic polynomial along any
fixed-loaded-level fast line, before using the equilibrium condition. -/
theorem loadedFastField_D_quadraticPath_raw {n : ℕ} (ET FT ST : ℝ)
    (k : Rates n) (u : CoordinateSpace n) (v : FastSpace n) (i : Fin n)
    (t : ℝ) :
    (loadedRestrictedField ET FT ST k (u + t • fastEmbed v)).2.2 i =
      (loadedRestrictedField ET FT ST k u).2.2 i +
      t * (k.alpha i *
        ((stateFromLoaded ET FT ST u).S i.succ * fastDeltaF v +
          (stateFromLoaded ET FT ST u).F * fastDeltaS v i.succ) -
        (k.beta i + k.gamma i) * v.2 i) +
      t ^ 2 * (k.alpha i * fastDeltaS v i.succ * fastDeltaF v) := by
  have h := loadedFastField_difference_D ET FT ST k u (t • v) i
  rw [fastEmbed_smul] at h
  rw [fastDeltaS_smul, fastDeltaF_smul] at h
  simp only [Prod.smul_snd, Pi.smul_apply, smul_eq_mul] at h
  calc
    (loadedRestrictedField ET FT ST k (u + t • fastEmbed v)).2.2 i =
        (k.alpha i *
          ((stateFromLoaded ET FT ST u).S i.succ * (t * fastDeltaF v) +
            (stateFromLoaded ET FT ST u).F * (t * fastDeltaS v i.succ) +
            (t * fastDeltaS v i.succ) * (t * fastDeltaF v)) -
          (k.beta i + k.gamma i) * (t * v.2 i)) +
          (loadedRestrictedField ET FT ST k u).2.2 i :=
      (sub_eq_iff_eq_add).mp h
    _ = (loadedRestrictedField ET FT ST k u).2.2 i +
        t * (k.alpha i *
          ((stateFromLoaded ET FT ST u).S i.succ * fastDeltaF v +
            (stateFromLoaded ET FT ST u).F * fastDeltaS v i.succ) -
          (k.beta i + k.gamma i) * v.2 i) +
        t ^ 2 * (k.alpha i * fastDeltaS v i.succ * fastDeltaF v) := by
      ring

end
end PhosphorylationStableCapacity
