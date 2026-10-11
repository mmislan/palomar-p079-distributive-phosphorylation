module
public import proofs.PhosphorylationStableCapacity.PaperFixedBindingRealization435
public import proofs.PhosphorylationStableCapacity.AllCurrentSchurPremises435
public import proofs.PhosphorylationStableCapacity.AllCurrentSchurSpectrum435
public import proofs.PhosphorylationStableCapacity.IntertwinedCharpoly

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section

open Filter PhosphorylationSharpness Matrix Polynomial
open scoped Topology

/-- The paper's `b=β=1` choice has the identical coalesced slow Schur
action on every inverse-response binding tangent as the already
verified positive realization. -/
theorem paperFixedBindingSchur_action_eventually (m : ℕ) :
    ∀ᶠ r : ℝ in atTop,
      ∀ w : Fin (m+2) → ℝ, (∀ i, 0 < w i) →
        let u := loadedCoordOfState (coalescedFiniteState (m+1) r)
        let k := paperFixedBindingRates (coalescedAllScaledRates m r w)
        let x := stateFromLoaded (2*r) 2 (2*(r+1)) u
        ∀ (hpos : x.Positive) (_heq : Equilibrium k x)
          (hρ : ∀ j : Fin (m+2), 0 < k.a j*x.S j.castSucc*x.E)
          (hσ : ∀ j : Fin (m+2), 0 < k.alpha j*x.S j.succ*x.F)
          (q : Fin (m+3) → ℝ), (∑ j, q j)=0 →
          schurLinear
            (loadedBlockA (2*r) 2 (2*(r+1)) k u).toLinearMap
            (loadedBlockB (2*r) 2 (2*(r+1)) k u).toLinearMap
            (loadedBlockC (2*r) 2 (2*(r+1)) k u).toLinearMap
            (fastBindingEquiv x hpos
              (fun j => k.a j*x.S j.castSucc*x.E)
              (fun j => k.alpha j*x.S j.succ*x.F) hρ hσ)
            (coalescedBindingCoordTangent m r q).1 =
              coalescedAllInverseSlowAction m r w q := by
  filter_upwards [coalescedAllLoadedFderiv_inverseResponse_eventually m,
    coalescedAllScaledRates_eventually_source m] with r haction hsource
  intro w hw u k x hpos heq hρ hσ q hq
  obtain ⟨hbasepos, _⟩ := hsource w hw
  let v := coalescedBindingCoordTangent m r q
  have hbase := haction w q hq
  have hpaper := paperFixedBindingRates_loadedFderiv_fastZero
    (2*r) 2 (2*(r+1)) (coalescedAllScaledRates m r w)
    hbasepos u v (coalescedAllInverseSlowAction m r w q) hbase
  have hblock := loadedFderiv_block_action
    (2*r) 2 (2*(r+1)) k u v.1 v.2
  have hv : (v.1, v.2) = v := by cases v; rfl
  rw [hv] at hblock
  change fderiv ℝ (loadedRestrictedField (2*r) 2 (2*(r+1)) k)
      u v = (coalescedAllInverseSlowAction m r w q,
        (0 : (Fin (m+2) → ℝ) × (Fin (m+2) → ℝ))) at hpaper
  rw [hblock] at hpaper
  have hslow := congrArg Prod.fst hpaper
  have hfast := congrArg Prod.snd hpaper
  dsimp only at hslow hfast
  have hSchur := loadedSchur_action_of_fast_zero
    (2*r) 2 (2*(r+1)) k u hpos heq hρ hσ v.1 v.2 hfast
  rw [hslow] at hSchur
  exact hSchur

/-- The projected-path intertwining for the exact fixed-binding paper
rates has the same current matrix, preserving every independent edge
current and the literal common coalesced state. -/
theorem paperFixedBindingSchur_intertwining_eventually (m : ℕ) :
    ∀ᶠ r : ℝ in atTop,
      ∀ w : Fin (m+2) → ℝ, (∀ i, 0 < w i) →
        let u := loadedCoordOfState (coalescedFiniteState (m+1) r)
        let k := paperFixedBindingRates (coalescedAllScaledRates m r w)
        let x := stateFromLoaded (2*r) 2 (2*(r+1)) u
        ∀ (hpos : x.Positive) (_heq : Equilibrium k x)
          (hρ : ∀ j : Fin (m+2), 0 < k.a j*x.S j.castSucc*x.E)
          (hσ : ∀ j : Fin (m+2), 0 < k.alpha j*x.S j.succ*x.F)
          (z : Fin (m+2) → ℝ),
          schurLinear
            (loadedBlockA (2*r) 2 (2*(r+1)) k u).toLinearMap
            (loadedBlockB (2*r) 2 (2*(r+1)) k u).toLinearMap
            (loadedBlockC (2*r) 2 (2*(r+1)) k u).toLinearMap
            (fastBindingEquiv x hpos
              (fun j => k.a j*x.S j.castSucc*x.E)
              (fun j => k.alpha j*x.S j.succ*x.F) hρ hσ)
            ((projectedPathIncidence (m+2)).mulVec z) =
              (projectedPathIncidence (m+2)).mulVec
                ((Matrix.diagonal w * coalescedFullLoadedMatrix m r).mulVec z) := by
  filter_upwards [paperFixedBindingSchur_action_eventually m,
    eventually_gt_atTop (0 : ℝ)] with r haction hr
  intro w hw u k x hpos heq hρ hσ z
  have h := haction w hw hpos heq hρ hσ
    ((coalescedFullEdgeForcingMatrix m).mulVec z)
    (coalescedFullEdgeForcing_sum_zero m z)
  rw [coalescedBindingCoordTangent_fullEdge_slow,
    coalescedAllInverseSlowAction_fullEdge] at h
  rw [map_smul] at h
  exact (smul_right_injective (Fin (m+2) → ℝ) hr.ne') h

/-- The paper fixed-binding rate list has exactly the same coalesced
Schur characteristic polynomial, hence the same simple neutral mode
and Hurwitz complement. -/
theorem paperFixedBindingSchur_charpoly_eventually (m : ℕ) :
    ∀ᶠ r : ℝ in atTop,
      ∀ w : Fin (m+2) → ℝ, (∀ i, 0 < w i) →
        let u := loadedCoordOfState (coalescedFiniteState (m+1) r)
        let k := paperFixedBindingRates (coalescedAllScaledRates m r w)
        let x := stateFromLoaded (2*r) 2 (2*(r+1)) u
        ∀ (hpos : x.Positive) (_heq : Equilibrium k x)
          (hρ : ∀ j : Fin (m+2), 0 < k.a j*x.S j.castSucc*x.E)
          (hσ : ∀ j : Fin (m+2), 0 < k.alpha j*x.S j.succ*x.F),
          (schurLinear
            (loadedBlockA (2*r) 2 (2*(r+1)) k u).toLinearMap
            (loadedBlockB (2*r) 2 (2*(r+1)) k u).toLinearMap
            (loadedBlockC (2*r) 2 (2*(r+1)) k u).toLinearMap
            (fastBindingEquiv x hpos
              (fun j => k.a j*x.S j.castSucc*x.E)
              (fun j => k.alpha j*x.S j.succ*x.F) hρ hσ)).charpoly =
            (coalescedFullLoadedMatrix m r * Matrix.diagonal w).charpoly := by
  filter_upwards [paperFixedBindingSchur_intertwining_eventually m]
    with r hinter
  intro w hw u k x hpos heq hρ hσ
  have hchar := charpoly_of_matrix_intertwining
    (schurLinear
      (loadedBlockA (2*r) 2 (2*(r+1)) k u).toLinearMap
      (loadedBlockB (2*r) 2 (2*(r+1)) k u).toLinearMap
      (loadedBlockC (2*r) 2 (2*(r+1)) k u).toLinearMap
      (fastBindingEquiv x hpos
        (fun j => k.a j*x.S j.castSucc*x.E)
        (fun j => k.alpha j*x.S j.succ*x.F) hρ hσ))
    (projectedPathIncidence (m+2))
    (Matrix.diagonal w * coalescedFullLoadedMatrix m r)
    (projectedPathIncidence_isUnit (m+2))
    (hinter w hw hpos heq hρ hσ)
  calc
    _ = (Matrix.diagonal w * coalescedFullLoadedMatrix m r).charpoly := hchar
    _ = (coalescedFullLoadedMatrix m r * Matrix.diagonal w).charpoly :=
      Matrix.charpoly_mul_comm (Matrix.diagonal w) (coalescedFullLoadedMatrix m r)

end

end PhosphorylationStableCapacity
