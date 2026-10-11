module
public import proofs.PhosphorylationStableCapacity.AllCurrentLoadedBlockAction435
public import proofs.PhosphorylationStableCapacity.CoalescedWeightedSchurPremises
public import proofs.PhosphorylationStableCapacity.LoadedSchurAction

@[expose] public section

namespace PhosphorylationStableCapacity

open Filter PhosphorylationSharpness

noncomputable section

/-- The Schur operator for the actual edge-retuned rate list acts on each
inverse-response loaded slow tangent as the weighted finite current
incidence response. Positive source premises are separately strict. -/
theorem coalescedAllSchur_action_eventually (m : ℕ) :
    ∀ᶠ r : ℝ in atTop,
      ∀ w : Fin (m + 2) → ℝ,
        let u := loadedCoordOfState (coalescedFiniteState (m + 1) r)
        let k := coalescedAllScaledRates m r w
        let x := stateFromLoaded (2 * r) 2 (2 * (r + 1)) u
        ∀ (hpos : x.Positive) (_heq : Equilibrium k x)
          (hρ : ∀ j : Fin (m + 2),
            0 < k.a j * x.S j.castSucc * x.E)
          (hσ : ∀ j : Fin (m + 2),
            0 < k.alpha j * x.S j.succ * x.F)
          (q : Fin (m + 3) → ℝ),
            (∑ l, q l) = 0 →
            schurLinear
              (loadedBlockA (2 * r) 2 (2 * (r + 1)) k u).toLinearMap
              (loadedBlockB (2 * r) 2 (2 * (r + 1)) k u).toLinearMap
              (loadedBlockC (2 * r) 2 (2 * (r + 1)) k u).toLinearMap
              (fastBindingEquiv x hpos
                (fun j => k.a j * x.S j.castSucc * x.E)
                (fun j => k.alpha j * x.S j.succ * x.F)
                hρ hσ)
              (coalescedBindingCoordTangent m r q).1 =
                coalescedAllInverseSlowAction m r w q := by
  filter_upwards [coalescedAllLoadedBlockAction_eventually m]
    with r hblock
  intro w u k x hpos heq hρ hσ q hq
  let v := coalescedBindingCoordTangent m r q
  obtain ⟨hslow, hfast⟩ := hblock w q hq
  have h := loadedSchur_action_of_fast_zero
    (2 * r) 2 (2 * (r + 1)) k u
    hpos heq hρ hσ v.1 v.2 hfast
  rw [hslow] at h
  exact h

end
end PhosphorylationStableCapacity
