module
public import proofs.PhosphorylationStableCapacity.CoalescedLoadedJacobianAction
public import proofs.PhosphorylationStableCapacity.LoadedJacobianBlockAction

@[expose] public section

namespace PhosphorylationStableCapacity

open Filter PhosphorylationSharpness

noncomputable section

/-- The coalesced inverse-response tangent solves the exact literal fast
block equation, and its slow block action is the finite current-incidence
response. -/
theorem coalescedLoadedBlockAction_eventually (m : ℕ) :
    ∀ᶠ r : ℝ in atTop,
      ∀ (q : Fin (m + 3) → ℝ),
        (∑ k, q k) = 0 →
        let u := loadedCoordOfState (coalescedFiniteState (m + 1) r)
        let v := coalescedBindingCoordTangent m r q
        loadedBlockA (2 * r) 2 (2 * (r + 1))
            (coalescedFiniteRates (m + 1) r) u v.1 +
          loadedBlockB (2 * r) 2 (2 * (r + 1))
            (coalescedFiniteRates (m + 1) r) u v.2 =
              coalescedInverseSlowAction m r q ∧
        loadedBlockC (2 * r) 2 (2 * (r + 1))
            (coalescedFiniteRates (m + 1) r) u v.1 +
          loadedBlockD (2 * r) 2 (2 * (r + 1))
            (coalescedFiniteRates (m + 1) r) u v.2 = 0 := by
  filter_upwards [coalescedLoadedFderiv_inverseResponse_eventually m]
    with r haction
  intro q hq
  let u := loadedCoordOfState (coalescedFiniteState (m + 1) r)
  let v := coalescedBindingCoordTangent m r q
  have hblock := loadedFderiv_block_action
    (2 * r) 2 (2 * (r + 1))
    (coalescedFiniteRates (m + 1) r) u v.1 v.2
  have hv : (v.1, v.2) = v := by cases v; rfl
  rw [hv] at hblock
  have h := haction q hq
  change fderiv ℝ
      (loadedRestrictedField (2 * r) 2 (2 * (r + 1))
        (coalescedFiniteRates (m + 1) r)) u v =
        (coalescedInverseSlowAction m r q,
          (0 : (Fin (m + 2) → ℝ) × (Fin (m + 2) → ℝ))) at h
  rw [hblock] at h
  exact ⟨congrArg Prod.fst h, congrArg Prod.snd h⟩

end
end PhosphorylationStableCapacity
