module
public import proofs.PhosphorylationStableCapacity.ReconstructCurveMagnitude
public import proofs.PhosphorylationStableCapacity.SplitChartTotalDerivatives

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section

open PhosphorylationSharpness Polynomial

/-- The exact moment bracket at a prescribed split state is proportional
to the physical substrate-total slope. This retains the magnitude that
the earlier orientation theorem discarded. -/
theorem splitChart_moment_magnitude_at_root
    (m : ℕ) (r δ : ℝ) (hδ : 0 ≤ δ)
    (hD : DensePositive (splitRawD m r δ) m)
    (hB : DensePositive (splitRawB m r δ) m)
    (j : Fin (2*m+1))
    (hv : 0 < r-ratio (splitRoot δ j.val)) :
    let x := splitFiniteState m r δ j
    let y₀ := splitRoot δ j.val
    let b := (y₀/4) / ratio y₀
    b * ((1-sourcePathFirstMoment (sourceOccupancyDifference x)) *
        sourcePathZerothMoment (sourceAugmentedTotalRow x) +
      sourcePathZerothMoment (sourceOccupancyDifference x) *
        sourcePathFirstMoment (sourceAugmentedTotalRow x)) =
      sourcePathZerothMoment (sourceOccupancyDifference x) *
        deriv (fun y => splitChartResidual m r δ y) y₀ := by
  dsimp only
  let y₀ := splitRoot δ j.val
  let U := splitChartU
  let S := splitChartS m r δ
  let F := splitChartF m r δ
  let t : Fin (m+2) → ℝ := fun i =>
    (((1+X)*splitRawD m r δ : ℝ[X]).coeff i)
  let B : Fin (m+1) → ℝ := fun i => (splitRawB m r δ).coeff i
  let D : Fin (m+1) → ℝ := fun i => (splitRawD m r δ).coeff i
  let x := splitFiniteState m r δ j
  have hy : 1 < y₀ := by
    have hh : 0 ≤ δ*(j.val : ℝ) :=
      mul_nonneg hδ (Nat.cast_nonneg _)
    dsimp [y₀, splitRoot]
    linarith
  have hu0 : 0 < U y₀ := ratio_pos hy
  have hd0 : 0 < (splitRawD m r δ).eval (U y₀) :=
    hD.eval_pos hu0
  have hell0 : 0 < (splitRawB m r δ).eval (U y₀) /
      (splitRawD m r δ).eval (U y₀)-r := by
    change 0 < (splitRawB m r δ).eval
      (ratio (splitRoot δ j.val)) /
        (splitRawD m r δ).eval (ratio (splitRoot δ j.val))-r
    rw [splitChartEll_eq_at_root m r δ j hy (ne_of_gt hd0)]
    exact div_pos (mul_pos (by norm_num) hv) (sub_pos.mpr hy)
  have hSpos : 0 < S y₀ := chartS_pos hu0 hd0 hell0 hv
  have hFpos : 0 < F y₀ := chartF_pos hell0 hv
  let a := deriv S y₀ / S y₀
  let b := (y₀/4) / U y₀
  let z := deriv F y₀ / F y₀
  have hu : HasDerivAt U (U y₀*b) y₀ := by
    have h := splitChartU_hasDerivAt y₀
    convert h using 1
    dsimp [b]
    field_simp [ne_of_gt hu0]
  have hs : HasDerivAt S (S y₀*a) y₀ := by
    have h := (splitChartS_differentiableAt m r δ y₀
      (ne_of_gt hu0) (ne_of_gt hd0) (ne_of_gt hell0)).hasDerivAt
    change HasDerivAt S (deriv S y₀) y₀ at h
    convert h using 1
    dsimp [a]
    field_simp [ne_of_gt hSpos]
  have hf : HasDerivAt F (F y₀*z) y₀ := by
    have hv0 : 0 < r-U y₀ := hv
    have hellv : 0 < (splitRawB m r δ).eval (U y₀) /
        (splitRawD m r δ).eval (U y₀)-U y₀ := by
      linarith [hell0, hv0]
    have h := (splitChartF_differentiableAt m r δ y₀
      (ne_of_gt hd0) (ne_of_gt hellv)).hasDerivAt
    change HasDerivAt F (deriv F y₀) y₀ at h
    convert h using 1
    dsimp [z]
    field_simp [ne_of_gt hFpos]
  obtain ⟨_, hx, _, _, _, _⟩ :=
    splitFiniteState_source_of_conversion_positive m r δ hδ hD hB j
  have hchart : reconstruct t B D (U y₀) (S y₀) (F y₀) = x := by
    rw [← splitChartState_eq_reconstruct]
    exact splitChartState_eq_finite_at_root m r δ j hy
      (ne_of_gt hd0) (ne_of_gt hv)
  obtain ⟨hET, hFT, hST⟩ :=
    splitChartState_total_derivatives_at_root m r δ j hD hB hy hv
  have hET' : HasDerivAt (fun y =>
      totalE (reconstruct t B D (U y) (S y) (F y))) 0 y₀ := by
    simpa only [U, S, F, t, B, D, splitChartState_eq_reconstruct]
      using hET
  have hFT' : HasDerivAt (fun y =>
      totalF (reconstruct t B D (U y) (S y) (F y))) 0 y₀ := by
    simpa only [U, S, F, t, B, D, splitChartState_eq_reconstruct]
      using hFT
  have hST' : HasDerivAt (fun y =>
      totalS (reconstruct t B D (U y) (S y) (F y)))
        (deriv (fun y => splitChartResidual m r δ y) y₀) y₀ := by
    simpa only [U, S, F, t, B, D, splitChartState_eq_reconstruct]
      using hST
  have hmoment := reconstructed_curve_moment_magnitude
    t B D U S F y₀ a b z
      (deriv (fun y => splitChartResidual m r δ y) y₀)
      (by rw [hchart]; exact hx) hu hs hf hET' hFT' hST'
  rw [hchart] at hmoment
  exact hmoment

end
end PhosphorylationStableCapacity
