module
public import proofs.PhosphorylationStableCapacity.ArbitrarySplitDetSign

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section

open PhosphorylationSharpness Polynomial

/-- Distinct prescribed roots make every split class equilibrium hyperbolic
    once the common transverse spectral condition is present. -/
theorem arbitrarySplit_jacobian_det_ne_zero_of_gap_ne_zero
    (m : ℕ) (ξ : ℕ → ℝ) (r δ : ℝ)
    (hr : 0 < r) (hδ : 0 < δ)
    (k : Rates (m+1)) (hk : k.Positive)
    (hD : DensePositive (arbitrarySplitRawD m ξ r δ) m)
    (hB : DensePositive (arbitrarySplitRawB m ξ r δ) m)
    (j : Fin (2*m+1))
    (hy : 1 < offsetSplitRoot ξ δ j.val)
    (hv : 0 < r-ratio (offsetSplitRoot ξ δ j.val))
    (heq : Equilibrium k (arbitrarySplitFiniteState m ξ r δ j))
    (hconversion : 0 < 4*r*(arbitrarySplitPair m ξ δ).1.eval r+
      (offsetSplitRoot ξ δ j.val-1)*
        (arbitrarySplitPair m ξ δ).2.eval r)
    (hgap : (∏ i ∈ (Finset.range (2*m+1)).erase j.val,
      (ξ j.val-ξ i)) ≠ 0) :
    let x := arbitrarySplitFiniteState m ξ r δ j
    let A := restrictedJacobianMatrix (totalE x) (totalF x) (totalS x)
      k (toCoordinateSpace (chart x))
    A.det ≠ 0 := by
  dsimp only
  let x := arbitrarySplitFiniteState m ξ r δ j
  let A := restrictedJacobianMatrix (totalE x) (totalF x) (totalS x)
    k (toCoordinateSpace (chart x))
  let D := LinearMap.toMatrix (fastBasis (m+1)) (fastBasis (m+1))
    (loadedBlockD (totalE x) (totalF x) (totalS x) k
      (loadedCoordOfState x)).toLinearMap
  let Q0 := sourcePathZerothMoment (sourceOccupancyDifference x)
  let y := offsetSplitRoot ξ δ j.val
  let chartFactor := chartConversionMultiplier y (r-ratio y)
    ((arbitrarySplitRawB m ξ r δ).eval (ratio y) /
      (arbitrarySplitRawD m ξ r δ).eval (ratio y)-r)
    ((arbitrarySplitRawD m ξ r δ).eval (ratio y))
  let conversionFactor :=
    4*r*(arbitrarySplitPair m ξ δ).1.eval r+
      (y-1)*(arbitrarySplitPair m ξ δ).2.eval r
  let rowprod := ∏ i : Fin (m+2), sourceAugmentedRowWeight k x i
  obtain ⟨_, hx, _, _, _, _⟩ :=
    arbitrarySplitFiniteState_source_of_conversion_positive
      m ξ r δ hD hB j hy
  have hback : stateFromLoaded (totalE x) (totalF x) (totalS x)
      (loadedCoordOfState x) = x :=
    stateFromLoaded_loadedCoordOfState _ _ _ x ⟨rfl, rfl, rfl⟩
  have hDdet : 0 < D.det := by
    have h := loaded_source_fast_block_det_pos
      (totalE x) (totalF x) (totalS x) k (loadedCoordOfState x) hk
      (by rw [hback]; exact hx) (by rw [hback]; exact heq)
    exact h
  have hrow : 0 < rowprod := sourceAugmentedRowWeight_prod_pos k x hk hx
  have hQ : Q0 < 0 :=
    arbitrarySplit_sourceOccupancyDifference_sum_neg
      m ξ r δ hr hD hB j hy hv
  have hd : 0 < (arbitrarySplitRawD m ξ r δ).eval (ratio y) :=
    hD.eval_pos (ratio_pos hy)
  have hell : 0 < (arbitrarySplitRawB m ξ r δ).eval (ratio y) /
      (arbitrarySplitRawD m ξ r δ).eval (ratio y)-r := by
    rw [arbitrarySplitChartEll_eq_at_root m ξ r δ j hy (ne_of_gt hd)]
    exact div_pos (mul_pos (by norm_num) hv) (sub_pos.mpr hy)
  have hchart : chartFactor < 0 :=
    chartConversionMultiplier_neg y (r-ratio y)
      ((arbitrarySplitRawB m ξ r δ).eval (ratio y) /
        (arbitrarySplitRawD m ξ r δ).eval (ratio y)-r)
      ((arbitrarySplitRawD m ξ r δ).eval (ratio y)) hy hv hell hd
  have hpow : 0 < δ^(2*m) := pow_pos hδ _
  have hR : D.det * rowprod *
      ((-1 : ℝ)^(m+1) *
        (Q0 * chartFactor * conversionFactor *
          (δ^(2*m) *
            ∏ i ∈ (Finset.range (2*m+1)).erase j.val,
              (ξ j.val-ξ i)))) ≠ 0 := by
    have hsign : (-1 : ℝ)^(m+1) ≠ 0 := pow_ne_zero _ (by norm_num)
    have hq : Q0 ≠ 0 := ne_of_lt hQ
    have hc : chartFactor ≠ 0 := ne_of_lt hchart
    exact mul_ne_zero (mul_ne_zero (ne_of_gt hDdet) (ne_of_gt hrow))
      (mul_ne_zero hsign
        (mul_ne_zero (mul_ne_zero (mul_ne_zero hq hc)
          (ne_of_gt hconversion))
          (mul_ne_zero (ne_of_gt hpow) hgap)))
  have hexact := arbitrarySplit_jacobian_exact_root_gap
    m ξ r δ k hk hD hB j hy hv heq
  change A.det * (sourceConstrainedBindingMass x).det *
      sourceAugmentedCurrentMatrix k x 0 0 * ((y/4)/ratio y) =
      D.det * rowprod *
        ((-1 : ℝ)^(m+1) *
          (Q0 * chartFactor * conversionFactor *
            (δ^(2*m) *
              ∏ i ∈ (Finset.range (2*m+1)).erase j.val,
                (ξ j.val-ξ i)))) at hexact
  intro hzero
  rw [hzero] at hexact
  simp only [zero_mul] at hexact
  exact hR hexact.symm

end
end PhosphorylationStableCapacity
