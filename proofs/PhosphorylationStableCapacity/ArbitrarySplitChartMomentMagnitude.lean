module
public import proofs.PhosphorylationStableCapacity.ArbitrarySplitChartTangent
public import proofs.PhosphorylationStableCapacity.ReconstructCurveMagnitude

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section

open PhosphorylationSharpness Polynomial

/-- The exact moment bracket for an arbitrary-offset prescribed root is
proportional to the physical substrate-total chart slope. -/
theorem arbitrarySplitChart_moment_magnitude_at_root
    (m : ℕ) (ξ : ℕ → ℝ) (r δ : ℝ)
    (hD : DensePositive (arbitrarySplitRawD m ξ r δ) m)
    (hB : DensePositive (arbitrarySplitRawB m ξ r δ) m)
    (j : Fin (2*m+1))
    (hy : 1 < offsetSplitRoot ξ δ j.val)
    (hv : 0 < r-ratio (offsetSplitRoot ξ δ j.val)) :
    let x := arbitrarySplitFiniteState m ξ r δ j
    let y₀ := offsetSplitRoot ξ δ j.val
    let b := (y₀/4) / ratio y₀
    b * ((1-sourcePathFirstMoment (sourceOccupancyDifference x)) *
        sourcePathZerothMoment (sourceAugmentedTotalRow x) +
      sourcePathZerothMoment (sourceOccupancyDifference x) *
        sourcePathFirstMoment (sourceAugmentedTotalRow x)) =
      sourcePathZerothMoment (sourceOccupancyDifference x) *
        deriv (fun y => arbitrarySplitChartResidual m ξ r δ y) y₀ := by
  dsimp only
  let y₀ := offsetSplitRoot ξ δ j.val
  let U := arbitrarySplitChartU
  let S := arbitrarySplitChartS m ξ r δ
  let F := arbitrarySplitChartF m ξ r δ
  let t : Fin (m+2) → ℝ := fun i =>
    (((1+X)*arbitrarySplitRawD m ξ r δ : ℝ[X]).coeff i)
  let B : Fin (m+1) → ℝ := fun i => (arbitrarySplitRawB m ξ r δ).coeff i
  let D : Fin (m+1) → ℝ := fun i => (arbitrarySplitRawD m ξ r δ).coeff i
  let x := arbitrarySplitFiniteState m ξ r δ j
  have hu0 : 0 < U y₀ := ratio_pos hy
  have hd0 : 0 < (arbitrarySplitRawD m ξ r δ).eval (U y₀) :=
    hD.eval_pos hu0
  have hell0 : 0 < (arbitrarySplitRawB m ξ r δ).eval (U y₀) /
      (arbitrarySplitRawD m ξ r δ).eval (U y₀)-r := by
    change 0 < (arbitrarySplitRawB m ξ r δ).eval
      (ratio (offsetSplitRoot ξ δ j.val)) /
        (arbitrarySplitRawD m ξ r δ).eval
          (ratio (offsetSplitRoot ξ δ j.val))-r
    rw [arbitrarySplitChartEll_eq_at_root m ξ r δ j hy (ne_of_gt hd0)]
    exact div_pos (mul_pos (by norm_num) hv) (sub_pos.mpr hy)
  have hSpos : 0 < S y₀ := chartS_pos hu0 hd0 hell0 hv
  have hFpos : 0 < F y₀ := chartF_pos hell0 hv
  let a := deriv S y₀ / S y₀
  let b := (y₀/4) / U y₀
  let z := deriv F y₀ / F y₀
  have hu : HasDerivAt U (U y₀*b) y₀ := by
    have h := arbitrarySplitChartU_hasDerivAt y₀
    convert h using 1
    dsimp [b]
    field_simp [ne_of_gt hu0]
  have hs : HasDerivAt S (S y₀*a) y₀ := by
    have h := (arbitrarySplitChartS_differentiableAt m ξ r δ y₀
      (ne_of_gt hu0) (ne_of_gt hd0) (ne_of_gt hell0)).hasDerivAt
    change HasDerivAt S (deriv S y₀) y₀ at h
    convert h using 1
    dsimp [a]
    field_simp [ne_of_gt hSpos]
  have hf : HasDerivAt F (F y₀*z) y₀ := by
    have hv0 : 0 < r-U y₀ := hv
    have hellv : 0 < (arbitrarySplitRawB m ξ r δ).eval (U y₀) /
        (arbitrarySplitRawD m ξ r δ).eval (U y₀)-U y₀ := by
      linarith [hell0, hv0]
    have h := (arbitrarySplitChartF_differentiableAt m ξ r δ y₀
      (ne_of_gt hd0) (ne_of_gt hellv)).hasDerivAt
    change HasDerivAt F (deriv F y₀) y₀ at h
    convert h using 1
    dsimp [z]
    field_simp [ne_of_gt hFpos]
  obtain ⟨_, hx, _, _, _, _⟩ :=
    arbitrarySplitFiniteState_source_of_conversion_positive
      m ξ r δ hD hB j hy
  have hchart : reconstruct t B D (U y₀) (S y₀) (F y₀) = x := by
    rw [← arbitrarySplitChartState_eq_reconstruct]
    exact arbitrarySplitChartState_eq_finite_at_root m ξ r δ j hy
      (ne_of_gt hd0) (ne_of_gt hv)
  obtain ⟨hET, hFT, hST⟩ :=
    arbitrarySplitChartState_total_derivatives_at_root
      m ξ r δ j hD hB hy hv
  have hET' : HasDerivAt (fun y =>
      totalE (reconstruct t B D (U y) (S y) (F y))) 0 y₀ := by
    simpa only [U, S, F, t, B, D,
      arbitrarySplitChartState_eq_reconstruct] using hET
  have hFT' : HasDerivAt (fun y =>
      totalF (reconstruct t B D (U y) (S y) (F y))) 0 y₀ := by
    simpa only [U, S, F, t, B, D,
      arbitrarySplitChartState_eq_reconstruct] using hFT
  have hST' : HasDerivAt (fun y =>
      totalS (reconstruct t B D (U y) (S y) (F y)))
        (deriv (fun y => arbitrarySplitChartResidual m ξ r δ y) y₀) y₀ := by
    simpa only [U, S, F, t, B, D,
      arbitrarySplitChartState_eq_reconstruct] using hST
  have hmoment := reconstructed_curve_moment_magnitude
    t B D U S F y₀ a b z
      (deriv (fun y => arbitrarySplitChartResidual m ξ r δ y) y₀)
      (by rw [hchart]; exact hx) hu hs hf hET' hFT' hST'
  rw [hchart] at hmoment
  exact hmoment

end
end PhosphorylationStableCapacity
