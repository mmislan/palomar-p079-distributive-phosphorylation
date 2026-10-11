module
public import proofs.PhosphorylationStableCapacity.ActualPrefixCurrentReparam435
public import proofs.PhosphorylationStableCapacity.CompactPaperFixedBindingFullJacobian435

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section

open PhosphorylationSharpness Filter
open scoped Topology

/-- For an arbitrary compact set of positive *actual* prefix catalytic
currents, choose one common positive final actual current and one
common binding scale. The manuscript's fixed-binding literal rates
realize those currents at the same coalesced state and have one simple
neutral class mode with all transverse modes strictly stable. -/
theorem compactActualCurrent_paperFixedBinding_coalesced_exists
    (m : ℕ) :
    ∀ᶠ r : ℝ in atTop,
      ∀ (K : Set (PositivePrefixCurrents m)), IsCompact K →
        ∃ t ε : ℝ, 0 < t ∧ 0 < ε ∧ ε ≤ 1 ∧
          ∀ ω ∈ K,
            let w := Fin.lastCases
              (t / (coalescedFiniteState (m+1) r).D (Fin.last (m+1)))
              (fun i => ω.val i /
                (coalescedFiniteState (m+1) r).D i.castSucc)
            let k := relaxRates (paperFixedBindingRates
              (coalescedAllScaledRates m r w)) ε
            (∀ i : Fin (m+1),
              k.gamma i.castSucc *
                (coalescedFiniteState (m+1) r).D i.castSucc = ω.val i) ∧
            k.gamma (Fin.last (m+1)) *
              (coalescedFiniteState (m+1) r).D (Fin.last (m+1)) = t ∧
            SimpleNeutralHurwitzComplement
              (restrictedJacobianMatrix (2*r) 2 (2*(r+1)) k
                (fromLoadedCoord (loadedCoordOfState
                  (coalescedFiniteState (m+1) r)))) := by
  filter_upwards [coalescedPaperFixedBinding_compact_spectrum_eventually m,
    coalescedFiniteState_eventually_equilibrium (m+1)]
    with r hspec hsource
  intro K hK
  have hx := hsource.2.1
  let Φ := edgePrefixFactorsOfActualCurrent m r hx
  let K' : Set (PositivePrefixCurrents m) := Φ '' K
  have hK' : IsCompact K' :=
    isCompact_edgePrefixFactorsOfActualCurrent_image m r hx K hK
  obtain ⟨τ, hτ, hτpos⟩ :=
    ((hspec K' hK').and self_mem_nhdsWithin).exists
  have hεsmall : ∀ᶠ ε : ℝ in 𝓝 (0 : ℝ), ε < 1 :=
    isOpen_Iio.mem_nhds (by norm_num)
  have hpositive : ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ), 0 < ε :=
    self_mem_nhdsWithin
  obtain ⟨ε, hεboth, hεpos⟩ :=
    (((hτ.filter_mono
      (nhdsWithin_le_nhds : 𝓝[>] (0 : ℝ) ≤ 𝓝 (0 : ℝ))).and
      (hεsmall.filter_mono
        (nhdsWithin_le_nhds : 𝓝[>] (0 : ℝ) ≤ 𝓝 (0 : ℝ)))).and
      hpositive).exists
  rcases hεboth with ⟨hε, hεlt⟩
  let Dlast := (coalescedFiniteState (m+1) r).D (Fin.last (m+1))
  have hDlast : 0 < Dlast := hx.2.2.2.2 (Fin.last (m+1))
  let t := τ*Dlast
  have ht : 0 < t := mul_pos hτpos hDlast
  refine ⟨t, ε, ht, hεpos, hεlt.le, ?_⟩
  intro ω hω
  have hΦ : Φ ω ∈ K' := ⟨ω, hω, rfl⟩
  have hτeq : t /
      (coalescedFiniteState (m+1) r).D (Fin.last (m+1)) = τ := by
    change t/Dlast = τ
    dsimp [t]
    exact mul_div_cancel_right₀ τ (ne_of_gt hDlast)
  have hprefix : (Φ ω).val =
      (fun i : Fin (m+1) => ω.val i /
        (coalescedFiniteState (m+1) r).D i.castSucc) := rfl
  have hspecω := hε hεpos (Φ ω) hΦ
  dsimp only
  constructor
  · intro i
    have hflux := paperFixedBinding_actual_prefix_current_eq
      m r t ε hx ω i
    simpa only [finalEdgeFactorOfActualCurrent,
      edgePrefixFactorsOfActualCurrent] using hflux
  constructor
  · have hfinal := paperFixedBinding_actual_final_current_eq
      m r t ε hx ω
    simpa only [finalEdgeFactorOfActualCurrent,
      edgePrefixFactorsOfActualCurrent] using hfinal
  · simpa only [hτeq, hprefix] using hspecω

end

end PhosphorylationStableCapacity
