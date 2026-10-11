module
public import proofs.PhosphorylationStableCapacity.AllCurrentSlowSchurDock435
public import proofs.PhosphorylationStableCapacity.CoalescedLoadedChartBase

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section

open Filter PhosphorylationSharpness Polynomial

/-- Every positive vector of edge-current scales realizes the same exact
coalesced equilibrium and conserved totals at all sufficiently large
finite source parameters. -/
theorem coalescedAllScaledRates_eventually_source (m : ℕ) :
    ∀ᶠ r : ℝ in atTop,
      ∀ (w : Fin (m+2) → ℝ), (∀ i, 0 < w i) →
        (coalescedAllScaledRates m r w).Positive ∧
          Equilibrium (coalescedAllScaledRates m r w)
            (coalescedFiniteState (m+1) r) := by
  have hdense := coalescedPair_dense (m+1)
  filter_upwards [coalescedFiniteState_eventually_equilibrium (m+1),
    conversion_eventually_positive hdense.1 hdense.2]
    with r hsource hBD
  obtain ⟨hk, _, heq, _, _, _⟩ := hsource
  intro w hw
  refine ⟨edgeScaledRates_positive _ _ hw hk, ?_⟩
  apply edgeScaledRates_equilibrium
  · intro i
    have h := heq.2.2.2.1 i
    change kinaseNet (coalescedFiniteRates (m+1) r)
      (coalescedFiniteState (m+1) r) i -
      (coalescedFiniteRates (m+1) r).c i *
        (coalescedFiniteState (m+1) r).C i = 0 at h
    exact sub_eq_zero.mp h
  · intro i
    have h := heq.2.2.2.2 i
    change phosphataseNet (coalescedFiniteRates (m+1) r)
      (coalescedFiniteState (m+1) r) i -
      (coalescedFiniteRates (m+1) r).gamma i *
        (coalescedFiniteState (m+1) r).D i = 0 at h
    exact sub_eq_zero.mp h
  · intro i
    exact realize_reconstruct_catalytic_balance
      (fun j : Fin (m+3) =>
        ((1 + Polynomial.X) * coalescedRawD (m+1) r).coeff j)
      (fun j : Fin (m+2) => (coalescedRawB (m+1) r).coeff j)
      (fun j : Fin (m+2) => (coalescedRawD (m+1) r).coeff j)
      (ratio 3)
      (rootS 3 ((coalescedRawD (m+1) r).eval (ratio 3)))
      (rootF 3) i
      (ne_of_gt (hBD.2.1 i (by omega)))

/-- The actual all-current rate realization supplies the positive-state,
equilibrium, and fast-binding premises required by the Schur and
singular-perturbation spectral bridges. -/
theorem coalescedAllSchurPremises_eventually (m : ℕ) :
    ∀ᶠ r : ℝ in atTop,
      ∀ (w : Fin (m+2) → ℝ), (∀ i, 0 < w i) →
        let u := loadedCoordOfState (coalescedFiniteState (m+1) r)
        let k := coalescedAllScaledRates m r w
        let x := stateFromLoaded (2*r) 2 (2*(r+1)) u
        x.Positive ∧ Equilibrium k x ∧
          (∀ i : Fin (m+2), 0 < k.a i * x.S i.castSucc * x.E) ∧
          (∀ i : Fin (m+2), 0 < k.alpha i * x.S i.succ * x.F) := by
  filter_upwards [coalescedFiniteState_eventually_equilibrium (m+1),
    coalescedAllScaledRates_eventually_source m,
    coalescedLoadedChartBase_eventually_eq_state m]
    with r hsource hscaled hchart
  intro w hw
  obtain ⟨_, hstate, _, _, _, _⟩ := hsource
  obtain ⟨hrates, heq⟩ := hscaled w hw
  let u := loadedCoordOfState (coalescedFiniteState (m+1) r)
  let k := coalescedAllScaledRates m r w
  have hpos : (stateFromLoaded (2*r) 2 (2*(r+1)) u).Positive := by
    rw [hchart]
    exact hstate
  have heq' : Equilibrium k
      (stateFromLoaded (2*r) 2 (2*(r+1)) u) := by
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
