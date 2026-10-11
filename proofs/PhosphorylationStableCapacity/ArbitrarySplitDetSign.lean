module
public import proofs.PhosphorylationStableCapacity.ArbitrarySplitJacobianMagnitude
public import proofs.PhosphorylationStableCapacity.ArbitrarySplitSpectrum
public import proofs.PhosphorylationStableCapacity.SplitDeterminantSlowSign

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section

open PhosphorylationSharpness Polynomial Filter
open scoped Topology

theorem arbitrarySplit_sourceOccupancyDifference_sum_neg
    (m : ℕ) (ξ : ℕ → ℝ) (r δ : ℝ) (hr : 0 < r)
    (hD : DensePositive (arbitrarySplitRawD m ξ r δ) m)
    (hB : DensePositive (arbitrarySplitRawB m ξ r δ) m)
    (j : Fin (2*m+1))
    (hx : 1 < offsetSplitRoot ξ δ j.val)
    (hv : 0 < r-ratio (offsetSplitRoot ξ δ j.val)) :
    sourcePathZerothMoment
      (sourceOccupancyDifference
        (arbitrarySplitFiniteState m ξ r δ j)) < 0 := by
  obtain ⟨_, hxpos, _, hET, hFT, _⟩ :=
    arbitrarySplitFiniteState_source_of_conversion_positive
      m ξ r δ hD hB j hx
  have hf : rootF (offsetSplitRoot ξ δ j.val) ≠ 0 := by
    unfold rootF
    exact ne_of_gt (div_pos (by norm_num) (by linarith))
  have hratio :
      (arbitrarySplitFiniteState m ξ r δ j).E /
        (arbitrarySplitFiniteState m ξ r δ j).F =
      ratio (offsetSplitRoot ξ δ j.val) := by
    exact reconstruct_ratio _ _ _ _ _ _ hf
  change (∑ l : Fin (m+2), sourceOccupancyDifference
    (arbitrarySplitFiniteState m ξ r δ j) l) < 0
  apply sourceOccupancyDifference_sum_neg_of_ratio
    (arbitrarySplitFiniteState m ξ r δ j) hxpos r hr hET hFT
  rw [hratio]
  linarith

theorem arbitrarySplitConversionPrefactor_eventually_pos
    (m : ℕ) (ξ : ℕ → ℝ) (r : ℝ) (hr : 0 < r)
    (j : Fin (2*m+1)) :
    ∀ᶠ δ : ℝ in 𝓝[>] (0 : ℝ),
      0 < 4*r*(arbitrarySplitPair m ξ δ).1.eval r+
        (offsetSplitRoot ξ δ j.val-1)*
          (arbitrarySplitPair m ξ δ).2.eval r := by
  let P : ℝ → ℝ := fun δ =>
    4*r*(arbitrarySplitPair m ξ δ).1.eval r+
      (offsetSplitRoot ξ δ j.val-1)*
        (arbitrarySplitPair m ξ δ).2.eval r
  have hP : Continuous P := by
    have hp := (arbitrarySplitPair_eval_continuous m ξ r).1
    have hq := (arbitrarySplitPair_eval_continuous m ξ r).2
    have hx : Continuous (fun δ : ℝ => offsetSplitRoot ξ δ j.val) := by
      dsimp [offsetSplitRoot]
      fun_prop
    have h : Continuous (fun δ : ℝ =>
        (4*r)*(arbitrarySplitPair m ξ δ).1.eval r+
          (offsetSplitRoot ξ δ j.val-1)*
            (arbitrarySplitPair m ξ δ).2.eval r) :=
      (continuous_const.mul hp).add
        ((hx.sub continuous_const).mul hq)
    convert h using 1
  have hzero : 0 < P 0 := by
    rw [show P 0 =
      4*r*(coalescedPair m).1.eval r+
        2*(coalescedPair m).2.eval r from
      arbitrarySplitConversionPrefactor_zero m ξ r j.val]
    exact arbitrarySplitConversionPrefactor_zero_pos m r hr
  exact (hP.tendsto 0).eventually (Ioi_mem_nhds hzero) |>.filter_mono
    nhdsWithin_le_nhds

/-- At any admissible arbitrary-root equilibrium, the parity-adjusted
literal Jacobian determinant has precisely the sign of the root-gap product. -/
theorem arbitrarySplit_jacobian_det_sign_iff_root_gap
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
        (arbitrarySplitPair m ξ δ).2.eval r) :
    let x := arbitrarySplitFiniteState m ξ r δ j
    let A := restrictedJacobianMatrix (totalE x) (totalF x) (totalS x)
      k (toCoordinateSpace (chart x))
    0 < (-1 : ℝ)^(m+1) * A.det ↔
      0 < ∏ i ∈ (Finset.range (2*m+1)).erase j.val,
        (ξ j.val-ξ i) := by
  dsimp only
  let x := arbitrarySplitFiniteState m ξ r δ j
  let A := restrictedJacobianMatrix (totalE x) (totalF x) (totalS x)
    k (toCoordinateSpace (chart x))
  let u := loadedCoordOfState x
  let D := LinearMap.toMatrix (fastBasis (m+1)) (fastBasis (m+1))
    (loadedBlockD (totalE x) (totalF x) (totalS x) k u).toLinearMap
  let M := sourceConstrainedBindingMass x
  let pivot := sourceAugmentedCurrentMatrix k x 0 0
  let Q0 := sourcePathZerothMoment (sourceOccupancyDifference x)
  let y₀ := offsetSplitRoot ξ δ j.val
  let b := (y₀/4) / ratio y₀
  let chartFactor := chartConversionMultiplier y₀ (r-ratio y₀)
    ((arbitrarySplitRawB m ξ r δ).eval (ratio y₀) /
      (arbitrarySplitRawD m ξ r δ).eval (ratio y₀)-r)
    ((arbitrarySplitRawD m ξ r δ).eval (ratio y₀))
  let conversionFactor :=
    4*r*(arbitrarySplitPair m ξ δ).1.eval r+
      (y₀-1)*(arbitrarySplitPair m ξ δ).2.eval r
  let rowprod := ∏ i : Fin (m+2), sourceAugmentedRowWeight k x i
  let gap := ∏ i ∈ (Finset.range (2*m+1)).erase j.val,
    (ξ j.val-ξ i)
  let s : ℝ := (-1)^(m+1)
  obtain ⟨_, hx, _, _, _, _⟩ :=
    arbitrarySplitFiniteState_source_of_conversion_positive
      m ξ r δ hD hB j hy
  have hback : stateFromLoaded (totalE x) (totalF x) (totalS x) u = x :=
    stateFromLoaded_loadedCoordOfState _ _ _ x ⟨rfl, rfl, rfl⟩
  have hDdet : 0 < D.det := by
    have h := loaded_source_fast_block_det_pos
      (totalE x) (totalF x) (totalS x) k u hk
      (by rw [hback]; exact hx) (by rw [hback]; exact heq)
    exact h
  have hMdet : 0 < M.det := sourceConstrainedBindingMass_det_pos x hx
  have hpivot : 0 < pivot := sourceAugmentedCurrentMatrix_pivot_pos k x hx
  have hrow : 0 < rowprod := sourceAugmentedRowWeight_prod_pos k x hk hx
  have hQ0 : Q0 < 0 :=
    arbitrarySplit_sourceOccupancyDifference_sum_neg
      m ξ r δ hr hD hB j hy hv
  have hd : 0 < (arbitrarySplitRawD m ξ r δ).eval (ratio y₀) :=
    hD.eval_pos (ratio_pos hy)
  have hell : 0 < (arbitrarySplitRawB m ξ r δ).eval (ratio y₀) /
      (arbitrarySplitRawD m ξ r δ).eval (ratio y₀)-r := by
    rw [arbitrarySplitChartEll_eq_at_root m ξ r δ j hy (ne_of_gt hd)]
    exact div_pos (mul_pos (by norm_num) hv) (sub_pos.mpr hy)
  have hchart : chartFactor < 0 :=
    chartConversionMultiplier_neg y₀ (r-ratio y₀)
      ((arbitrarySplitRawB m ξ r δ).eval (ratio y₀) /
        (arbitrarySplitRawD m ξ r δ).eval (ratio y₀)-r)
      ((arbitrarySplitRawD m ξ r δ).eval (ratio y₀)) hy hv hell hd
  have hb : 0 < b := div_pos (div_pos (by linarith) (by norm_num))
    (ratio_pos hy)
  have hcon : 0 < conversionFactor := hconversion
  have hpow : 0 < δ^(2*m) := pow_pos hδ _
  have hden : 0 < M.det*pivot*b := by positivity
  have hnegQ : 0 < -Q0 := by linarith
  have hnegChart : 0 < -chartFactor := by linarith
  have hpos : 0 < D.det*rowprod*((-Q0)*(-chartFactor)*conversionFactor*δ^(2*m)) := by
    positivity
  have hexact := arbitrarySplit_jacobian_exact_root_gap
    m ξ r δ k hk hD hB j hy hv heq
  change A.det*M.det*pivot*b =
    D.det*rowprod*(s*(Q0*chartFactor*conversionFactor*(δ^(2*m)*gap)))
    at hexact
  have hs2 : s*s = 1 := by
    dsimp [s]
    rw [← mul_pow]
    norm_num
  have heqsign : (s*A.det)*(M.det*pivot*b) =
      (D.det*rowprod*((-Q0)*(-chartFactor)*conversionFactor*δ^(2*m)))*gap := by
    calc
      (s*A.det)*(M.det*pivot*b) =
          s*(A.det*M.det*pivot*b) := by ring
      _ = s*(D.det*rowprod*(s*(Q0*chartFactor*conversionFactor*
            (δ^(2*m)*gap)))) := by rw [hexact]
      _ = (s*s)*(D.det*rowprod*Q0*chartFactor*conversionFactor*
            δ^(2*m)*gap) := by ring
      _ = (D.det*rowprod*((-Q0)*(-chartFactor)*conversionFactor*
            δ^(2*m)))*gap := by rw [hs2]; ring
  rw [← mul_pos_iff_of_pos_right hden, heqsign,
    mul_pos_iff_of_pos_left hpos]

end
end PhosphorylationStableCapacity
