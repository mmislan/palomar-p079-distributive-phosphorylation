module
public import proofs.PhosphorylationStableCapacity.CoalescedFinalRateRetune
public import proofs.PhosphorylationStableCapacity.CoalescedLoadedChartBase

@[expose] public section

namespace PhosphorylationStableCapacity

open Filter PhosphorylationSharpness

noncomputable section

theorem coalescedWeightedSchurPremises_eventually (m : ℕ) :
    ∀ᶠ r : ℝ in atTop,
      ∀ τ : ℝ, 0 < τ →
        let u := loadedCoordOfState (coalescedFiniteState (m + 1) r)
        let k := coalescedFinalScaledRates m r τ
        let x := stateFromLoaded (2 * r) 2 (2 * (r + 1)) u
        x.Positive ∧ Equilibrium k x ∧
          (∀ i : Fin (m + 2),
            0 < k.a i * x.S i.castSucc * x.E) ∧
          (∀ i : Fin (m + 2),
            0 < k.alpha i * x.S i.succ * x.F) := by
  filter_upwards [coalescedFiniteState_eventually_equilibrium (m + 1),
    coalescedFinalScaledRates_eventually_source m,
    coalescedLoadedChartBase_eventually_eq_state m]
    with r hsource hscaled hchart
  intro τ hτ
  obtain ⟨_, hstate, _, _, _, _⟩ := hsource
  obtain ⟨hrates, heq⟩ := hscaled τ hτ
  let u := loadedCoordOfState (coalescedFiniteState (m + 1) r)
  let k := coalescedFinalScaledRates m r τ
  have hpos : (stateFromLoaded (2 * r) 2 (2 * (r + 1)) u).Positive := by
    rw [hchart]
    exact hstate
  have heq' : Equilibrium k
      (stateFromLoaded (2 * r) 2 (2 * (r + 1)) u) := by
    rw [hchart]
    exact heq
  refine ⟨hpos, heq', ?_, ?_⟩
  · intro i
    rw [hchart]
    obtain ⟨ha, _, _, _, _, _⟩ := hrates i
    exact mul_pos (mul_pos ha (hstate.1 i.castSucc)) hstate.2.1
  · intro i
    rw [hchart]
    obtain ⟨_, _, _, halpha, _, _⟩ := hrates i
    exact mul_pos (mul_pos halpha (hstate.1 i.succ)) hstate.2.2.1

end
end PhosphorylationStableCapacity
