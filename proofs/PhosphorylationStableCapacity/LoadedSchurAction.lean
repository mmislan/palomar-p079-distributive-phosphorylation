module
public import proofs.PhosphorylationStableCapacity.LoadedFastBlockLinear
public import proofs.PhosphorylationStableCapacity.FastSlowSchurAlgebra
public import proofs.PhosphorylationStableCapacity.FastBindingInverse

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section
open PhosphorylationSharpness

/-- For a tangent that annihilates the literal fast rows, the exact loaded
Schur operator equals the literal slow-row derivative along that tangent. -/
theorem loadedSchur_action_of_fast_zero {n : ℕ}
    (ET FT ST : ℝ) (k : Rates n) (u : CoordinateSpace n)
    (hpos : (stateFromLoaded ET FT ST u).Positive)
    (heq : Equilibrium k (stateFromLoaded ET FT ST u))
    (hρ : ∀ j : Fin n,
      0 < k.a j * (stateFromLoaded ET FT ST u).S j.castSucc *
        (stateFromLoaded ET FT ST u).E)
    (hσ : ∀ j : Fin n,
      0 < k.alpha j * (stateFromLoaded ET FT ST u).S j.succ *
        (stateFromLoaded ET FT ST u).F)
    (s : SlowSpace n) (f : FastSpace n)
    (hfast : loadedBlockC ET FT ST k u s +
      loadedBlockD ET FT ST k u f = 0) :
    schurLinear
      (loadedBlockA ET FT ST k u).toLinearMap
      (loadedBlockB ET FT ST k u).toLinearMap
      (loadedBlockC ET FT ST k u).toLinearMap
      (fastBindingEquiv (stateFromLoaded ET FT ST u) hpos
        (fun j => k.a j * (stateFromLoaded ET FT ST u).S j.castSucc *
          (stateFromLoaded ET FT ST u).E)
        (fun j => k.alpha j * (stateFromLoaded ET FT ST u).S j.succ *
          (stateFromLoaded ET FT ST u).F) hρ hσ) s =
      loadedBlockA ET FT ST k u s + loadedBlockB ET FT ST k u f := by
  have hD := loadedBlockD_toLinearMap_eq_fastBinding
    ET FT ST k u hpos heq
  have hfast' :
      loadedBlockC ET FT ST k u s +
        fastBindingEquiv (stateFromLoaded ET FT ST u) hpos
          (fun j => k.a j * (stateFromLoaded ET FT ST u).S j.castSucc *
            (stateFromLoaded ET FT ST u).E)
          (fun j => k.alpha j * (stateFromLoaded ET FT ST u).S j.succ *
            (stateFromLoaded ET FT ST u).F) hρ hσ f = 0 := by
    have hdf := congrArg (fun L : FastSpace n →ₗ[ℝ] FastSpace n => L f) hD
    have hdeq : loadedBlockD ET FT ST k u f =
        fastBindingEquiv (stateFromLoaded ET FT ST u) hpos
          (fun j => k.a j * (stateFromLoaded ET FT ST u).S j.castSucc *
            (stateFromLoaded ET FT ST u).E)
          (fun j => k.alpha j * (stateFromLoaded ET FT ST u).S j.succ *
            (stateFromLoaded ET FT ST u).F) hρ hσ f := by
      simpa only [fastBindingEquiv_apply, fastBindingEnd,
        LinearMap.coe_mk, AddHom.coe_mk,
        ContinuousLinearMap.coe_coe] using hdf
    rw [← hdeq]
    exact hfast
  exact schurLinear_apply_of_fast_zero
    (loadedBlockA ET FT ST k u).toLinearMap
    (loadedBlockB ET FT ST k u).toLinearMap
    (loadedBlockC ET FT ST k u).toLinearMap
    (fastBindingEquiv (stateFromLoaded ET FT ST u) hpos
      (fun j => k.a j * (stateFromLoaded ET FT ST u).S j.castSucc *
        (stateFromLoaded ET FT ST u).E)
      (fun j => k.alpha j * (stateFromLoaded ET FT ST u).S j.succ *
        (stateFromLoaded ET FT ST u).F) hρ hσ) s f hfast'

end
end PhosphorylationStableCapacity
