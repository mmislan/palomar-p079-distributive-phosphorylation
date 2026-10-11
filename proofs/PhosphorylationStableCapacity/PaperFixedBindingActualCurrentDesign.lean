module
public import proofs.PhosphorylationStableCapacity.PaperFixedBindingFullSpectrum435
public import proofs.PhosphorylationStableCapacity.ActualPrefixCurrentReparam435
public import proofs.PhosphorylationStableCapacity.DyadicEventuallySelection
public import proofs.PhosphorylationStableCapacity.AllCurrentSchurPremises435

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section

open PhosphorylationSharpness Filter Polynomial
open scoped Topology

/-- The manuscript's `ω=(1,…,1,t)` coalesced kinetic choice. We first
select the large source parameter, then divide each prescribed actual
current by its positive coalesced phosphatase complex to freeze the
literal catalytic scale `θᵢ=ωᵢ/Yᵢ(X₀)`. -/
theorem paperFixedBinding_actual_unit_current_design (m : ℕ) :
    ∃ a b c : ℕ,
      let r : ℝ := (2 : ℝ)^a
      let t : ℝ := (1/2 : ℝ)^b
      let ε : ℝ := (1/2 : ℝ)^c
      let x := coalescedFiniteState (m+1) r
      let τ : ℝ := t / x.D (Fin.last (m+1))
      let θ : Fin (m+1) → ℝ := fun i => 1 / x.D i.castSucc
      let k := relaxRates (paperFixedBindingRates
        (coalescedAllScaledRates m r (Fin.lastCases τ θ))) ε
      1 < r ∧ (3*(m+2 : ℝ))/2 ≤ r ∧
      0 < t ∧ 0 < τ ∧ 0 < ε ∧ ε ≤ 1 ∧
      DensePositive (coalescedRawD (m+1) r) (m+1) ∧
      DensePositive (coalescedRawB (m+1) r) (m+1) ∧
      (∀ i, 0 < θ i) ∧
      (coalescedAllScaledRates m r (Fin.lastCases τ θ)).Positive ∧
      k.Positive ∧ x.Positive ∧ Equilibrium k x ∧
      totalE x = 2*r ∧ totalF x = 2 ∧
      SimpleNeutralHurwitzComplement
        (restrictedJacobianMatrix (2*r) 2 (2*(r+1)) k
          (fromLoadedCoord (loadedCoordOfState x))) ∧
      (∀ i : Fin (m+1), k.gamma i.castSucc * x.D i.castSucc = 1) ∧
      k.gamma (Fin.last (m+1)) * x.D (Fin.last (m+1)) = t := by
  obtain ⟨hp, hq⟩ := coalescedPair_dense (m+1)
  have hconv := conversion_eventually_positive hp hq
  have hr1 : ∀ᶠ r : ℝ in atTop, 1 < r := eventually_gt_atTop 1
  have hrAdequate : ∀ᶠ r : ℝ in atTop,
      (3*(m+2 : ℝ))/2 < r :=
    eventually_gt_atTop ((3*(m+2 : ℝ))/2)
  obtain ⟨a, hR⟩ := eventually_atTop_has_doubling_index _
    ((((paperFixedBindingRestrictedJacobian_spectrum_eventually m).and
      (coalescedAllScaledRates_eventually_source m)).and
      (coalescedFiniteState_eventually_equilibrium (m+1))).and
      (hconv.and (hr1.and hrAdequate)))
  rcases hR with
    ⟨⟨⟨hspecR, hsourceR⟩, hstateR⟩,
      ⟨hconvR, ⟨hr, hrAdequateNow⟩⟩⟩
  let r : ℝ := (2 : ℝ)^a
  let x := coalescedFiniteState (m+1) r
  obtain ⟨_, hx, _, hET, hFT, _⟩ := hstateR
  let ωactual : PositivePrefixCurrents m :=
    ⟨fun _ => 1, fun _ => by norm_num⟩
  let θpos := edgePrefixFactorsOfActualCurrent m r hx ωactual
  let θ : Fin (m+1) → ℝ := θpos.val
  have hθ : ∀ i, 0 < θ i := θpos.property
  have hθeq (i : Fin (m+1)) : θ i = 1 / x.D i.castSucc := rfl
  let Dlast : ℝ := x.D (Fin.last (m+1))
  have hDlast : 0 < Dlast := hx.2.2.2.2 (Fin.last (m+1))
  have hτmap : Tendsto (fun t : ℝ => t / Dlast)
      (𝓝[>] (0 : ℝ)) (𝓝[>] (0 : ℝ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · have hcont : ContinuousAt (fun t : ℝ => t / Dlast) 0 :=
        continuousAt_id.div_const Dlast
      simpa using hcont.tendsto.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with t ht
      exact div_pos ht hDlast
  have htpos : ∀ᶠ t : ℝ in 𝓝[>] (0 : ℝ), 0 < t :=
    self_mem_nhdsWithin
  obtain ⟨b, hspecτ, ht⟩ :=
    eventually_right_has_halving_index _
      ((hτmap.eventually (hspecR θ hθ)).and htpos)
  let t : ℝ := (1/2 : ℝ)^b
  let τ : ℝ := t / Dlast
  have hτ : 0 < τ := div_pos ht hDlast
  have hεpos : ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ), 0 < ε :=
    self_mem_nhdsWithin
  have hεle : ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ), ε ≤ 1 := by
    have hnear : ∀ᶠ ε : ℝ in 𝓝 (0 : ℝ), ε < 1 :=
      Iio_mem_nhds (by norm_num)
    exact (hnear.filter_mono nhdsWithin_le_nhds).mono
      (fun _ h => h.le)
  obtain ⟨c, ⟨hspecε, hε⟩, hεle⟩ :=
    eventually_right_has_halving_index _
      (((hspecτ.filter_mono nhdsWithin_le_nhds).and hεpos).and hεle)
  let ε : ℝ := (1/2 : ℝ)^c
  let w : Fin (m+2) → ℝ := Fin.lastCases τ θ
  let k₀ := coalescedAllScaledRates m r w
  let k := relaxRates (paperFixedBindingRates k₀) ε
  have hw : ∀ i : Fin (m+2), 0 < w i := by
    intro i
    cases i using Fin.lastCases with
    | last => simpa [w] using hτ
    | cast i => simpa [w] using hθ i
  obtain ⟨hbase, heqbase⟩ := hsourceR w hw
  have hfixed : (paperFixedBindingRates k₀).Positive :=
    paperFixedBindingRates_positive k₀ hbase
  have hk : k.Positive := relaxRates_positive _ hfixed hε hεle
  have heqfixed : Equilibrium (paperFixedBindingRates k₀) x :=
    paperFixedBindingRates_preserves_equilibrium k₀ x hbase heqbase
  have heq : Equilibrium k x :=
    relaxRates_preserves_equilibrium _ _ (ne_of_gt hε) heqfixed
  have hprefix (i : Fin (m+1)) :
      k.gamma i.castSucc * x.D i.castSucc = 1 := by
    have h := coalesced_actual_prefix_current_eq
      m r τ ε hx ωactual i
    simpa only [k, k₀, w, θ, ωactual,
      paperFixedBindingRates, relaxRates] using h
  have hfinal : k.gamma (Fin.last (m+1)) *
      x.D (Fin.last (m+1)) = t := by
    have h := coalesced_actual_final_current_eq m r τ ε θpos
    have hcancel : τ * x.D (Fin.last (m+1)) = t := by
      exact div_mul_cancel₀ t (ne_of_gt hDlast)
    simpa only [k, k₀, w, θ, paperFixedBindingRates,
      relaxRates] using h.trans hcancel
  refine ⟨a, b, c, hr, hrAdequateNow.le, ht, hτ, hε, hεle,
    hconvR.1, hconvR.2, ?_, ?_, hk, hx, heq,
    hET, hFT, hspecε hε, hprefix, hfinal⟩
  · intro i
    simpa only [hθeq i] using hθ i
  · exact hbase

end
end PhosphorylationStableCapacity
