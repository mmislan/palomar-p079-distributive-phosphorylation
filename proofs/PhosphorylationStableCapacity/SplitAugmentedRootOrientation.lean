module
public import proofs.PhosphorylationStableCapacity.SplitChartTotalDerivatives

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section
open PhosphorylationSharpness Polynomial

/-- Every even prescribed split root has the positive augmented
total/current determinant orientation required by the stable
attainment theorem, before kinetic retuning. -/
theorem split_even_source_augmented_current_det_pos
    (m : ℕ) (r δ : ℝ) (j : Fin (2*m+1))
    (hr : 0 < r) (hδ : 0 < δ)
    (hD : DensePositive (splitRawD m r δ) m)
    (hB : DensePositive (splitRawB m r δ) m)
    (hv : 0 < r-ratio (splitRoot δ j.val))
    (heven : Even j.val) :
    0 < (-1 : ℝ)^(m+1) *
      (sourceAugmentedCurrentMatrix (splitFiniteRates m r δ)
        (splitFiniteState m r δ j)).det := by
  let y0 := splitRoot δ j.val
  let U := splitChartU
  let S := splitChartS m r δ
  let F := splitChartF m r δ
  let t : Fin (m+2) → ℝ := fun i =>
    (((1+X)*splitRawD m r δ : ℝ[X]).coeff i)
  let B : Fin (m+1) → ℝ := fun i => (splitRawB m r δ).coeff i
  let D : Fin (m+1) → ℝ := fun i => (splitRawD m r δ).coeff i
  have hx0 : 1 < y0 := by
    have hnonneg : 0 ≤ δ*(j.val : ℝ) :=
      mul_nonneg hδ.le (Nat.cast_nonneg _)
    dsimp [y0, splitRoot]
    linarith
  have hu0 : 0 < U y0 := ratio_pos hx0
  have hd0 : 0 < (splitRawD m r δ).eval (U y0) :=
    hD.eval_pos hu0
  have hell0 : 0 < (splitRawB m r δ).eval (U y0) /
      (splitRawD m r δ).eval (U y0)-r := by
    change 0 < (splitRawB m r δ).eval (ratio y0) /
      (splitRawD m r δ).eval (ratio y0)-r
    rw [splitChartEll_eq_at_root m r δ j hx0 (ne_of_gt hd0)]
    exact div_pos (mul_pos (by norm_num) hv) (sub_pos.mpr hx0)
  have hellv0 : 0 < (splitRawB m r δ).eval (U y0) /
      (splitRawD m r δ).eval (U y0)-U y0 := by
    have hv0 : 0 < r-U y0 := by
      simpa only [U, splitChartU, y0] using hv
    linarith
  have hS0 : 0 < S y0 := by
    dsimp [S, splitChartS, U, splitChartU]
    exact chartS_pos hu0 hd0 hell0 hv
  have hF0 : 0 < F y0 := by
    dsimp [F, splitChartF, U, splitChartU]
    exact chartF_pos hell0 hv
  have hSd : DifferentiableAt ℝ S y0 :=
    splitChartS_differentiableAt m r δ y0
      (ne_of_gt hu0) (ne_of_gt hd0) (ne_of_gt hell0)
  have hFd : DifferentiableAt ℝ F y0 :=
    splitChartF_differentiableAt m r δ y0
      (ne_of_gt hd0) (ne_of_gt hellv0)
  let a := deriv S y0 / S y0
  let b := (y0/4) / U y0
  let z := deriv F y0 / F y0
  let H := deriv (fun y => splitChartResidual m r δ y) y0
  have hu : HasDerivAt U (U y0*b) y0 := by
    convert splitChartU_hasDerivAt y0 using 1
    dsimp [b]
    field_simp [ne_of_gt hu0]
  have hs : HasDerivAt S (S y0*a) y0 := by
    convert hSd.hasDerivAt using 1
    dsimp [a]
    field_simp [ne_of_gt hS0]
  have hf : HasDerivAt F (F y0*z) y0 := by
    convert hFd.hasDerivAt using 1
    dsimp [z]
    field_simp [ne_of_gt hF0]
  have hb : 0 < b :=
    div_pos (div_pos (by linarith : 0 < y0) (by norm_num)) hu0
  obtain ⟨hk, hx, _, _, _, _⟩ :=
    splitFiniteState_source_of_conversion_positive m r δ hδ.le hD hB j
  have hchart : splitChartState m r δ y0 =
      splitFiniteState m r δ j :=
    splitChartState_eq_finite_at_root m r δ j hx0
      (ne_of_gt hd0) (ne_of_gt hv)
  have hxcurve : (reconstruct t B D (U y0) (S y0) (F y0)).Positive := by
    change (splitChartState m r δ y0).Positive
    rw [hchart]
    exact hx
  have hq : sourcePathZerothMoment
      (sourceOccupancyDifference
        (reconstruct t B D (U y0) (S y0) (F y0))) < 0 := by
    change (∑ l : Fin (m+2), sourceOccupancyDifference
      (splitChartState m r δ y0) l) < 0
    rw [hchart]
    exact split_sourceOccupancyDifference_sum_neg
      m r δ hr hδ.le hD hB j hv
  obtain ⟨hET, hFT, hST⟩ :=
    splitChartState_total_derivatives_at_root m r δ j hD hB hx0 hv
  have hH : H < 0 :=
    (splitChartResidual_deriv_alternates m r δ j hr hδ hD hv).1 heven
  have hcurve := reconstructed_curve_augmented_orientation
    (splitFiniteRates m r δ) t B D U S F y0 a b z H
    hk hxcurve hu hs hf hb hq
    (by simpa only [splitChartState_eq_reconstruct] using hET)
    (by simpa only [splitChartState_eq_reconstruct] using hFT)
    (by simpa only [splitChartState_eq_reconstruct] using hST)
    hH
  change 0 < (-1 : ℝ)^(m+1) *
    (sourceAugmentedCurrentMatrix (splitFiniteRates m r δ)
      (splitChartState m r δ y0)).det at hcurve
  rw [hchart] at hcurve
  exact hcurve

end
end PhosphorylationStableCapacity
