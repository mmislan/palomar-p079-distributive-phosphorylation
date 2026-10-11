module
public import proofs.PhosphorylationStableCapacity.PaperFixedBindingCompactRateProduct435
public import proofs.PhosphorylationStableCapacity.PaperFixedBindingGeometricFactor435
public import proofs.PhosphorylationStableCapacity.UniformFixedFactorProductFirstOrder435

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section

open PhosphorylationSharpness Filter
open scoped Topology

/-- One first-order numerator bound for the actual manuscript
fixed-binding physical determinant over a compact family of positive
full-edge factors.  The same rate vector is used in the split count,
literal class Jacobian, and printed splitting coefficient. -/
theorem paperFixedBinding_compact_physicalPrefactor_first_order
    (m : ℕ) (ξ : ℕ → ℝ) (r ε : ℝ)
    (K : Set (Fin (m+2) → ℝ)) (hK : IsCompact K)
    (hKpos : ∀ w ∈ K, ∀ i, 0 < w i)
    (hr : 1 < r) (hε : 0 < ε)
    (hD₀ : DensePositive (coalescedRawD (m+1) r) (m+1))
    (hB₀ : DensePositive (coalescedRawB (m+1) r) (m+1))
    (hbase0 : (arbitrarySplitFiniteRates (m+1) ξ r 0).Positive)
    (hsource : ∀ᶠ δ : ℝ in 𝓝 0,
      (arbitrarySplitFiniteRates (m+1) ξ r δ).Positive)
    (j : Fin (2*(m+1)+1))
    (hstate0 :
      (arbitrarySplitFiniteState (m+1) ξ r 0 j).S 0 *
      (arbitrarySplitFiniteState (m+1) ξ r 0 j).E *
      (arbitrarySplitFiniteState (m+1) ξ r 0 j).F ≠ 0) :
    ∃ C : ℝ, 0 < C ∧
      ∀ᶠ δ : ℝ in 𝓝 0,
        ∀ w ∈ K,
          |arbitrarySplitGenericPhysicalPrefactor m ξ r δ
              (paperFixedBindingSplitRates m ξ r δ ε w) j -
            arbitrarySplitGenericPhysicalPrefactor m ξ r 0
              (paperFixedBindingSplitRates m ξ r 0 ε w) j| ≤
                C*|δ| := by
  let G := arbitrarySplitGeometricFactor m ξ r j
  let H (w : Fin (m+2) → ℝ) (δ : ℝ) : ℝ :=
    ∏ i : Fin (m+2),
      let k := paperFixedBindingSplitRates m ξ r δ ε w
      (k.b i+k.c i)*k.alpha i*k.gamma i
  have hGdiff : DifferentiableAt ℝ G 0 :=
    arbitrarySplitGeometricFactor_differentiableAt
      m ξ r hr hD₀ j hstate0
  obtain ⟨Cg, hCg, hGfirst⟩ :=
    differentiableAt_first_order_abs_bound G hGdiff
  obtain ⟨Ch, hCh, hHfirst⟩ :=
    paperFixedBinding_compact_physical_rateProduct_first_order
      m ξ r ε K hK hKpos (by linarith : r ≠ 0) hε
      hD₀ hB₀ hbase0 hsource
  obtain ⟨B, hB, hHzero⟩ :=
    paperFixedBinding_compact_physical_rateProduct_zero_upper
      m ξ r ε K hK hKpos hbase0
  obtain ⟨C, hC, hproduct⟩ :=
    uniform_fixed_factor_product_first_order
      K G H Cg Ch B hCg.le hCh.le hB.le
      hGfirst hHfirst hHzero
  refine ⟨C, hC, ?_⟩
  filter_upwards [hproduct] with δ hd w hw
  have hidentity (s : ℝ) :
      arbitrarySplitGenericPhysicalPrefactor m ξ r s
        (paperFixedBindingSplitRates m ξ r s ε w) j =
        G s * H w s := by
    simpa only [G, H] using
      arbitrarySplitGenericPhysicalPrefactor_eq_geometric_mul_rateProduct
        m ξ r s (paperFixedBindingSplitRates m ξ r s ε w) j
  rw [hidentity δ, hidentity 0]
  exact hd w hw

end

end PhosphorylationStableCapacity
