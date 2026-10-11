module
public import proofs.PhosphorylationStableCapacity.FastBindingHurwitz
public import proofs.PhosphorylationStableCapacity.LoadedFastBlockIdentification

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section
open PhosphorylationSharpness

/-- At a positive literal equilibrium, the loaded class Jacobian's fast-fast
block is the binding matrix and is Hurwitz. -/
theorem loadedFastBlock_identified_and_hurwitz {n : ℕ}
    (ET FT ST : ℝ) (k : Rates n) (hk : k.Positive)
    (u : CoordinateSpace n)
    (hpos : (stateFromLoaded ET FT ST u).Positive)
    (heq : Equilibrium k (stateFromLoaded ET FT ST u)) :
    (∀ v : FastSpace n,
      (fderiv ℝ (loadedRestrictedField ET FT ST k) u (fastEmbed v)).2 =
        fastBindingEnd n (stateFromLoaded ET FT ST u)
          (fun j => k.a j * (stateFromLoaded ET FT ST u).S j.castSucc *
            (stateFromLoaded ET FT ST u).E)
          (fun j => k.alpha j * (stateFromLoaded ET FT ST u).S j.succ *
            (stateFromLoaded ET FT ST u).F) v) ∧
    IsHurwitz (fastBindingMatrix n (stateFromLoaded ET FT ST u)
      (fun j => k.a j * (stateFromLoaded ET FT ST u).S j.castSucc *
        (stateFromLoaded ET FT ST u).E)
      (fun j => k.alpha j * (stateFromLoaded ET FT ST u).S j.succ *
        (stateFromLoaded ET FT ST u).F)) := by
  let x := stateFromLoaded ET FT ST u
  let rho : Fin n → ℝ := fun j => k.a j * x.S j.castSucc * x.E
  let sigma : Fin n → ℝ := fun j => k.alpha j * x.S j.succ * x.F
  have hρ : ∀ j, 0 < rho j := by
    intro j
    exact (equilibrium_binding_fluxes_positive k x hk hpos j).1
  have hσ : ∀ j, 0 < sigma j := by
    intro j
    exact (equilibrium_binding_fluxes_positive k x hk hpos j).2
  refine ⟨?_, fastBindingMatrix_hurwitz x hpos rho sigma hρ hσ⟩
  intro v
  exact loadedFastBlock_eq_fastBinding ET FT ST k u v hpos heq

end
end PhosphorylationStableCapacity
