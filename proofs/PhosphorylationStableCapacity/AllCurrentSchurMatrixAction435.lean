module
public import proofs.PhosphorylationStableCapacity.AllCurrentIncidenceAction435
public import proofs.PhosphorylationStableCapacity.CoalescedWeightedSchurPremises

@[expose] public section

namespace PhosphorylationStableCapacity

open Filter PhosphorylationSharpness

noncomputable section

/-- The literal edge-retuned Schur operator intertwines with the
row-weighted complete finite current matrix. -/
theorem coalescedAllSchur_intertwining_eventually (m : ℕ) :
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
          (z : Fin (m + 2) → ℝ),
            schurLinear
              (loadedBlockA (2 * r) 2 (2 * (r + 1)) k u).toLinearMap
              (loadedBlockB (2 * r) 2 (2 * (r + 1)) k u).toLinearMap
              (loadedBlockC (2 * r) 2 (2 * (r + 1)) k u).toLinearMap
              (fastBindingEquiv x hpos
                (fun j => k.a j * x.S j.castSucc * x.E)
                (fun j => k.alpha j * x.S j.succ * x.F)
                hρ hσ)
              ((projectedPathIncidence (m + 2)).mulVec z) =
                (projectedPathIncidence (m + 2)).mulVec
                  (((Matrix.diagonal (w)) *
                    (coalescedFullLoadedMatrix m r)).mulVec z) := by
  filter_upwards [coalescedAllSchur_action_eventually m,
    eventually_gt_atTop (0 : ℝ)] with r haction hr
  intro w u k x hpos heq hρ hσ z
  have h := haction w hpos heq hρ hσ
    ((coalescedFullEdgeForcingMatrix m).mulVec z)
    (coalescedFullEdgeForcing_sum_zero m z)
  rw [coalescedBindingCoordTangent_fullEdge_slow,
    coalescedAllInverseSlowAction_fullEdge] at h
  rw [map_smul] at h
  exact (smul_right_injective (Fin (m + 2) → ℝ) hr.ne') h

end
end PhosphorylationStableCapacity
