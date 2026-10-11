module
public import proofs.PhosphorylationStableCapacity.AllCurrentLoadedJacobianAction435
public import proofs.PhosphorylationStableCapacity.LoadedJacobianBlockAction

@[expose] public section

namespace PhosphorylationStableCapacity

open Filter PhosphorylationSharpness

noncomputable section

theorem coalescedAllLoadedBlockAction_eventually (m : ℕ) :
    ∀ᶠ r : ℝ in atTop,
      ∀ (w : Fin (m + 2) → ℝ) (q : Fin (m + 3) → ℝ),
        (∑ k, q k) = 0 →
        let u := loadedCoordOfState (coalescedFiniteState (m + 1) r)
        let v := coalescedBindingCoordTangent m r q
        loadedBlockA (2 * r) 2 (2 * (r + 1))
            (coalescedAllScaledRates m r w) u v.1 +
          loadedBlockB (2 * r) 2 (2 * (r + 1))
            (coalescedAllScaledRates m r w) u v.2 =
              coalescedAllInverseSlowAction m r w q ∧
        loadedBlockC (2 * r) 2 (2 * (r + 1))
            (coalescedAllScaledRates m r w) u v.1 +
          loadedBlockD (2 * r) 2 (2 * (r + 1))
            (coalescedAllScaledRates m r w) u v.2 = 0 := by
  filter_upwards [coalescedAllLoadedFderiv_inverseResponse_eventually m]
    with r haction
  intro w q hq
  let u := loadedCoordOfState (coalescedFiniteState (m + 1) r)
  let v := coalescedBindingCoordTangent m r q
  have hblock := loadedFderiv_block_action
    (2 * r) 2 (2 * (r + 1))
    (coalescedAllScaledRates m r w) u v.1 v.2
  have hv : (v.1, v.2) = v := by cases v; rfl
  rw [hv] at hblock
  have h := haction w q hq
  change fderiv ℝ
      (loadedRestrictedField (2 * r) 2 (2 * (r + 1))
        (coalescedAllScaledRates m r w)) u v =
        (coalescedAllInverseSlowAction m r w q,
          (0 : (Fin (m + 2) → ℝ) × (Fin (m + 2) → ℝ))) at h
  rw [hblock] at h
  exact ⟨congrArg Prod.fst h, congrArg Prod.snd h⟩

end
end PhosphorylationStableCapacity
