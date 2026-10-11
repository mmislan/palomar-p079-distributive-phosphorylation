module
public import proofs.PhosphorylationStableCapacity.ArbitrarySplitStateContinuity

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section

open PhosphorylationSharpness Filter
open scoped Topology

/-- Strict positivity of the coalesced source rates persists on a
signed split-parameter neighborhood. This supplies the literal
denominator-safe tube used by the compact fixed-binding derivative
and positive-probe estimates. -/
theorem arbitrarySplitFiniteRates_positive_signed_near_zero
    (m : ℕ) (ξ : ℕ → ℝ) (r : ℝ)
    (hr : r ≠ 0)
    (hD₀ : DensePositive (coalescedRawD (m+1) r) (m+1))
    (hB₀ : DensePositive (coalescedRawB (m+1) r) (m+1))
    (hbase0 : (coalescedFiniteRates (m+1) r).Positive) :
    ∀ᶠ δ : ℝ in 𝓝 0,
      (arbitrarySplitFiniteRates (m+1) ξ r δ).Positive := by
  have hper (i : Fin (m+2)) : ∀ᶠ δ : ℝ in 𝓝 0,
      0 < (arbitrarySplitFiniteRates (m+1) ξ r δ).a i ∧
      0 < (arbitrarySplitFiniteRates (m+1) ξ r δ).b i ∧
      0 < (arbitrarySplitFiniteRates (m+1) ξ r δ).c i ∧
      0 < (arbitrarySplitFiniteRates (m+1) ξ r δ).alpha i ∧
      0 < (arbitrarySplitFiniteRates (m+1) ξ r δ).beta i ∧
      0 < (arbitrarySplitFiniteRates (m+1) ξ r δ).gamma i := by
    obtain ⟨ha, hb, hc, hα, hβ, hγ⟩ :=
      arbitrarySplitFiniteRates_components_continuousAt
        (m+1) ξ r hr hD₀ hB₀ i
    have hzero :
        0 < (arbitrarySplitFiniteRates (m+1) ξ r 0).a i ∧
        0 < (arbitrarySplitFiniteRates (m+1) ξ r 0).b i ∧
        0 < (arbitrarySplitFiniteRates (m+1) ξ r 0).c i ∧
        0 < (arbitrarySplitFiniteRates (m+1) ξ r 0).alpha i ∧
        0 < (arbitrarySplitFiniteRates (m+1) ξ r 0).beta i ∧
        0 < (arbitrarySplitFiniteRates (m+1) ξ r 0).gamma i := by
      simpa only [arbitrarySplitFiniteRates_zero_eq_coalesced]
        using hbase0 i
    filter_upwards [ha.eventually (Ioi_mem_nhds hzero.1),
      hb.eventually (Ioi_mem_nhds hzero.2.1),
      hc.eventually (Ioi_mem_nhds hzero.2.2.1),
      hα.eventually (Ioi_mem_nhds hzero.2.2.2.1),
      hβ.eventually (Ioi_mem_nhds hzero.2.2.2.2.1),
      hγ.eventually (Ioi_mem_nhds hzero.2.2.2.2.2)]
      with δ haδ hbδ hcδ hαδ hβδ hγδ
    exact ⟨haδ, hbδ, hcδ, hαδ, hβδ, hγδ⟩
  exact Filter.eventually_all.mpr hper

end

end PhosphorylationStableCapacity
