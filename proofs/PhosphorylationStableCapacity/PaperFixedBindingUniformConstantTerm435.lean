module
public import proofs.PhosphorylationStableCapacity.PaperFixedBindingSplitCount435
public import proofs.PhosphorylationStableCapacity.ArbitrarySplitGenericPhysical435
public import proofs.PhosphorylationStableCapacity.ArbitrarySplitStateContinuity

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section

open PhosphorylationSharpness Filter Polynomial
open scoped Topology

/-- The exact physical characteristic constant-term factorization
holds on one split interval for every positive full-edge current
factor. The interval depends only on the source split geometry, not
on the current family or the selected root index. -/
theorem paperFixedBinding_uniform_constantTerm_root_gap
    (m : ℕ) (ξ : ℕ → ℝ) (r ε : ℝ)
    (hr : 1 < r) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hD₀ : DensePositive (coalescedRawD (m+1) r) (m+1))
    (hB₀ : DensePositive (coalescedRawB (m+1) r) (m+1))
    (j : Fin (2*(m+1)+1)) :
    ∀ᶠ δ : ℝ in 𝓝[>] (0 : ℝ),
      ∀ w : Fin (m+2) → ℝ, (∀ i, 0 < w i) →
        let k := paperFixedBindingSplitRates m ξ r δ ε w
        (restrictedJacobianMatrix (2*r) 2 (2*(r+1)) k
          (toCoordinateSpace (chart
            (arbitrarySplitFiniteState (m+1) ξ r δ j)))).charpoly.eval 0 =
          arbitrarySplitGenericPhysicalPrefactor m ξ r δ k j *
            δ^(2*(m+1)) *
              (∏ i ∈ (Finset.range (2*(m+1)+1)).erase j.val,
                (ξ j.val-ξ i)) := by
  have hconv := arbitrarySplit_conversion_positive_near_zero
    (m+1) ξ r (by linarith : r ≠ 0) hD₀ hB₀
  have hy : ∀ᶠ δ : ℝ in 𝓝[>] (0 : ℝ),
      1 < offsetSplitRoot ξ δ j.val := by
    have h := offsetSplitRoot_gt_one_eventually (m+1) ξ
    filter_upwards [h.filter_mono nhdsWithin_le_nhds] with δ hd
    exact hd j.val (by omega)
  have hv : ∀ᶠ δ : ℝ in 𝓝[>] (0 : ℝ),
      0 < r-ratio (offsetSplitRoot ξ δ j.val) := by
    have hcont : ContinuousAt
        (fun δ : ℝ => r-ratio (offsetSplitRoot ξ δ j.val)) 0 := by
      unfold ratio offsetSplitRoot
      fun_prop
    have hzero :
        0 < r-ratio (offsetSplitRoot ξ 0 j.val) := by
      norm_num [ratio, offsetSplitRoot]
      linarith
    exact (hcont.eventually (Ioi_mem_nhds hzero)).filter_mono
      nhdsWithin_le_nhds
  filter_upwards [hconv, hy, hv] with δ hconvδ hyδ hvδ w hw
  obtain ⟨hk, _, heq, hclass⟩ :=
    paperFixedBindingSplit_source m ξ r δ ε w hw hε hε1
      hconvδ.1 hconvδ.2 j hyδ
  have hphysical := arbitrarySplitGeneric_charpoly_constant_root_gap
    m ξ r δ (paperFixedBindingSplitRates m ξ r δ ε w)
      hk hconvδ.1 hconvδ.2 j hyδ hvδ heq
      hclass.1 hclass.2.1 hclass.2.2
  dsimp only
  rw [← Polynomial.coeff_zero_eq_eval_zero]
  simpa only [mul_assoc] using hphysical

end

end PhosphorylationStableCapacity
