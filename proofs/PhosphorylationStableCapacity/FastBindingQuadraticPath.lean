module
public import proofs.PhosphorylationStableCapacity.FastBindingScaling

@[expose] public section
set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

namespace PhosphorylationStableCapacity

noncomputable section
open PhosphorylationSharpness

private theorem quadraticPath_rearrange (b rho q a ds de t : ℝ) :
    (-rho * (t * q) + a * (t * ds) * (t * de)) + b =
      b + t * (-rho * q) + t ^ 2 * (a * ds * de) := by
  ring

/-- Along a fast line, the literal kinase-complex velocity is exactly a
quadratic polynomial with the equilibrium affinity as its linear term. -/
theorem loadedFastField_C_quadraticPath {n : ℕ} (ET FT ST : ℝ)
    (k : Rates n) (u : CoordinateSpace n) (v : FastSpace n) (i : Fin n)
    (hpos : (stateFromLoaded ET FT ST u).Positive)
    (heq : Equilibrium k (stateFromLoaded ET FT ST u)) (t : ℝ) :
    (loadedRestrictedField ET FT ST k (u + t • fastEmbed v)).2.1 i =
      (loadedRestrictedField ET FT ST k u).2.1 i +
      t * (-(k.a i * (stateFromLoaded ET FT ST u).S i.castSucc *
        (stateFromLoaded ET FT ST u).E) *
        fastAffinityC (stateFromLoaded ET FT ST u) v i) +
      t ^ 2 * (k.a i * fastDeltaS v i.castSucc * fastDeltaE v) := by
  have h := loadedFastField_difference_C_affinity ET FT ST k u
    (t • v) i hpos heq
  rw [fastEmbed_smul] at h
  rw [← fastAffinityC_eq_delta (stateFromLoaded ET FT ST u) (t • v) i,
    fastAffinityC_smul, fastDeltaS_smul, fastDeltaE_smul] at h
  calc
    (loadedRestrictedField ET FT ST k (u + t • fastEmbed v)).2.1 i =
        (-(k.a i * (stateFromLoaded ET FT ST u).S i.castSucc *
          (stateFromLoaded ET FT ST u).E) *
          (t * fastAffinityC (stateFromLoaded ET FT ST u) v i) +
          k.a i * (t * fastDeltaS v i.castSucc) *
            (t * fastDeltaE v)) +
          (loadedRestrictedField ET FT ST k u).2.1 i :=
      (sub_eq_iff_eq_add).mp h
    _ = (loadedRestrictedField ET FT ST k u).2.1 i +
        t * (-(k.a i * (stateFromLoaded ET FT ST u).S i.castSucc *
          (stateFromLoaded ET FT ST u).E) *
          fastAffinityC (stateFromLoaded ET FT ST u) v i) +
        t ^ 2 * (k.a i * fastDeltaS v i.castSucc * fastDeltaE v) :=
      quadraticPath_rearrange _ _ _ _ _ _ _

end
end PhosphorylationStableCapacity
