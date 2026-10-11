module
public import proofs.PhosphorylationStableCapacity.ReconstructCurveOrientation
public import proofs.PhosphorylationStableCapacity.SplitAugmentedRootOrientation

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section
open PhosphorylationSharpness Matrix Polynomial

/-- The opposite total slope reverses the augmented determinant sign. -/
theorem sourceAugmentedCurrentMatrix_parity_det_neg_of_affine_slope_pos
    {n : ℕ} (k : Rates n) (x : State n)
    (hk : k.Positive) (hx : x.Positive)
    (a b : ℝ) (hb : 0 < b)
    (hq : sourcePathZerothMoment (sourceOccupancyDifference x) < 0)
    (hkernel : a * sourcePathZerothMoment (sourceOccupancyDifference x) +
      b * (sourcePathFirstMoment (sourceOccupancyDifference x) - 1) = 0)
    (hslope : 0 < a * sourcePathZerothMoment (sourceAugmentedTotalRow x) +
      b * sourcePathFirstMoment (sourceAugmentedTotalRow x)) :
    (-1 : ℝ)^n * (sourceAugmentedCurrentMatrix k x).det < 0 := by
  let T0 := sourcePathZerothMoment (sourceAugmentedTotalRow x)
  let T1 := sourcePathFirstMoment (sourceAugmentedTotalRow x)
  let Q0 := sourcePathZerothMoment (sourceOccupancyDifference x)
  let Q1 := sourcePathFirstMoment (sourceOccupancyDifference x)
  have hker' : b * (1 - Q1) = a * Q0 := by
    dsimp [Q0, Q1] at hkernel ⊢
    linarith
  have hid : b * ((1 - Q1) * T0 + Q0 * T1) =
      Q0 * (a * T0 + b * T1) := by
    calc
      _ = (b * (1 - Q1)) * T0 + b * Q0 * T1 := by ring
      _ = (a * Q0) * T0 + b * Q0 * T1 := by rw [hker']
      _ = _ := by ring
  have hbracket : (1 - Q1) * T0 + Q0 * T1 < 0 := by
    have hmul : b * ((1 - Q1) * T0 + Q0 * T1) < 0 := by
      rw [hid]
      exact mul_neg_of_neg_of_pos hq hslope
    by_contra h
    have hnonneg : 0 ≤ (1 - Q1) * T0 + Q0 * T1 := le_of_not_gt h
    have := mul_nonneg hb.le hnonneg
    linarith
  have hdet := sourceAugmentedCurrentMatrix_parity_det_pos_iff_moment
    k x hk hx
  have h0 := ne_of_gt (sourceAugmentedTotalRow_zeroth_pos x hx)
  have hprod := sourceAugmentedRowWeight_prod_pos k x hk hx
  have hpow : (-1 : ℝ)^n * (-1 : ℝ)^n = 1 := by
    rw [← pow_add, show n + n = 2 * n by omega, pow_mul]
    norm_num
  rw [sourceAugmentedCurrentMatrix_det_rank_one k x h0]
  have heq : (-1 : ℝ)^n *
      ((∏ i : Fin (n+1), sourceAugmentedRowWeight k x i) *
        ((-1 : ℝ)^n *
          ((1 - Q1) * T0 + Q0 * T1))) =
      (∏ i : Fin (n+1), sourceAugmentedRowWeight k x i) *
        ((1 - Q1) * T0 + Q0 * T1) := by
    calc
      _ = (∏ i : Fin (n+1), sourceAugmentedRowWeight k x i) *
          (((-1 : ℝ)^n * (-1 : ℝ)^n) *
            ((1 - Q1) * T0 + Q0 * T1)) := by ring
      _ = _ := by rw [hpow, one_mul]
  rw [heq]
  exact mul_neg_of_pos_of_neg hprod hbracket

theorem sourceAugmentedCurrentMatrix_parity_det_neg_of_affine_tangent
    {n : ℕ} (k : Rates n) (x : State n)
    (hk : k.Positive) (hx : x.Positive)
    (a b : ℝ) (hb : 0 < b)
    (hq : sourcePathZerothMoment (sourceOccupancyDifference x) < 0)
    (hcurrent : a * (∑ j : Fin (n+1), sourceOccupancyDifference x j) +
      b * (sourceOccupancyFirstMoment x - 1) = 0)
    (htotal : 0 < sourceAugmentedTotalRow x ⬝ᵥ
      sourceAffineLogTangent a b) :
    (-1 : ℝ)^n * (sourceAugmentedCurrentMatrix k x).det < 0 := by
  apply sourceAugmentedCurrentMatrix_parity_det_neg_of_affine_slope_pos
    k x hk hx a b hb hq
  · simpa only [sourcePathZerothMoment,
      sourceOccupancyFirstMoment_eq_path] using hcurrent
  · simpa only [sourceAugmentedTotalRow_affine_action] using htotal


/-- Increasing substrate total reverses the physical source orientation. -/
theorem reconstructed_curve_augmented_orientation_neg {n : ℕ}
    (k : Rates n) (t : Fin (n+1) → ℝ) (B D : Fin n → ℝ)
    (u s f : ℝ → ℝ) (y a b z H : ℝ)
    (hk : k.Positive)
    (hx : (reconstruct t B D (u y) (s y) (f y)).Positive)
    (hu : HasDerivAt u (u y*b) y)
    (hs : HasDerivAt s (s y*a) y)
    (hf : HasDerivAt f (f y*z) y)
    (hb : 0 < b)
    (hq : sourcePathZerothMoment
      (sourceOccupancyDifference
        (reconstruct t B D (u y) (s y) (f y))) < 0)
    (hET : HasDerivAt (fun v =>
      totalE (reconstruct t B D (u v) (s v) (f v))) 0 y)
    (hFT : HasDerivAt (fun v =>
      totalF (reconstruct t B D (u v) (s v) (f v))) 0 y)
    (hST : HasDerivAt (fun v =>
      totalS (reconstruct t B D (u v) (s v) (f v))) H y)
    (hH : 0 < H) :
    (-1 : ℝ)^n *
      (sourceAugmentedCurrentMatrix k
        (reconstruct t B D (u y) (s y) (f y))).det < 0 := by
  let x : State n := reconstruct t B D (u y) (s y) (f y)
  let σ : Fin (n+1) → ℝ := sourceAffineLogTangent a b
  let curve : ℝ → State n := fun v =>
    reconstruct t B D (u v) (s v) (f v)
  have hCsum : HasDerivAt (fun v => ∑ i : Fin n, (curve v).C i)
      (∑ i : Fin n, x.C i * (σ i.succ+z)) y := by
    apply HasDerivAt.fun_sum
    intro i _
    exact hasDerivAt_reconstruct_kinase_complex t B D u s f y a b z
      hu hs hf i
  have hDsum : HasDerivAt (fun v => ∑ i : Fin n, (curve v).D i)
      (∑ i : Fin n, x.D i * (σ i.succ+z)) y := by
    apply HasDerivAt.fun_sum
    intro i _
    exact hasDerivAt_reconstruct_phosphatase_complex t B D u s f y a b z
      hu hs hf i
  have hSsum : HasDerivAt (fun v => ∑ j : Fin (n+1), (curve v).S j)
      (∑ j : Fin (n+1), x.S j * σ j) y := by
    apply HasDerivAt.fun_sum
    intro j _
    exact hasDerivAt_reconstruct_substrate t B D u s f y a b hu hs j
  have hEn : HasDerivAt (fun v => totalE (curve v))
      (x.E*(b+z) + ∑ i : Fin n, x.C i*(σ i.succ+z)) y := by
    have hfun :
        (fun v => (reconstruct t B D (u v) (s v) (f v)).E) +
          (fun v => ∑ i : Fin n, (curve v).C i) =
        (fun v => totalE (curve v)) := by
      funext v
      simp [totalE, curve, Pi.add_apply]
    have h :=
      (hasDerivAt_reconstruct_kinase_enzyme t B D u s f y b z
        hu hf).add hCsum
    rw [hfun] at h
    exact h
  have hFn : HasDerivAt (fun v => totalF (curve v))
      (x.F*z + ∑ i : Fin n, x.D i*(σ i.succ+z)) y := by
    have hfun :
        (fun v => (reconstruct t B D (u v) (s v) (f v)).F) +
          (fun v => ∑ i : Fin n, (curve v).D i) =
        (fun v => totalF (curve v)) := by
      funext v
      simp [totalF, curve, Pi.add_apply]
    have h :=
      (hasDerivAt_reconstruct_phosphatase_enzyme t B D u s f y z
        hf).add hDsum
    rw [hfun] at h
    exact h
  have hSn : HasDerivAt (fun v => totalS (curve v))
      ((∑ j : Fin (n+1), x.S j*σ j) +
        (∑ i : Fin n, x.C i*(σ i.succ+z)) +
        (∑ i : Fin n, x.D i*(σ i.succ+z))) y := by
    have hfun :
        ((fun v => ∑ j : Fin (n+1), (curve v).S j) +
          (fun v => ∑ i : Fin n, (curve v).C i)) +
          (fun v => ∑ i : Fin n, (curve v).D i) =
        (fun v => totalS (curve v)) := by
      funext v
      simp [totalS, Pi.add_apply]
    have h := (hSsum.add hCsum).add hDsum
    rw [hfun] at h
    exact h
  have hEzero : x.E*(b+z) +
      ∑ i : Fin n, x.C i*(σ i.succ+z) = 0 :=
    hEn.unique hET
  have hFzero : x.F*z +
      ∑ i : Fin n, x.D i*(σ i.succ+z) = 0 :=
    hFn.unique hFT
  have hshift (i : Fin n) : σ i.succ = σ i.castSucc + b := by
    simp [σ, sourceAffineLogTangent]
    ring
  have hEbal : totalE x*(b+z) +
      ∑ i : Fin n, x.C i*σ i.castSucc = 0 := by
    simp_rw [hshift] at hEzero
    simp only [← add_assoc, mul_add, Finset.sum_add_distrib,
      ← Finset.sum_mul] at hEzero
    dsimp [totalE]
    linear_combination hEzero
  have hFbal : totalF x*z +
      ∑ i : Fin n, x.D i*σ i.succ = 0 := by
    simp only [mul_add, Finset.sum_add_distrib,
      ← Finset.sum_mul] at hFzero
    dsimp [totalF]
    linear_combination hFzero
  have hcurrent := source_affine_current_kernel_of_enzyme_balances
    x hx a b z hEbal hFbal
  have hspecies := source_affine_species_total_eq_loaded_action
    x hx a b z hEbal hFbal
  have htotal : 0 < sourceAugmentedTotalRow x ⬝ᵥ σ := by
    have hderiv := hSn.unique hST
    rw [hspecies] at hderiv
    rw [hderiv]
    exact hH
  exact sourceAugmentedCurrentMatrix_parity_det_neg_of_affine_tangent
    k x hk hx a b hb hq hcurrent htotal


/-- Odd split roots have the reversed physical source orientation. -/
theorem split_odd_source_augmented_current_det_neg
    (m : ℕ) (r δ : ℝ) (j : Fin (2*m+1))
    (hr : 0 < r) (hδ : 0 < δ)
    (hD : DensePositive (splitRawD m r δ) m)
    (hB : DensePositive (splitRawB m r δ) m)
    (hv : 0 < r-ratio (splitRoot δ j.val))
    (hodd : Odd j.val) :
    (-1 : ℝ)^(m+1) *
      (sourceAugmentedCurrentMatrix (splitFiniteRates m r δ)
        (splitFiniteState m r δ j)).det < 0 := by
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
  have hH : 0 < H :=
    (splitChartResidual_deriv_alternates m r δ j hr hδ hD hv).2 hodd
  have hcurve := reconstructed_curve_augmented_orientation_neg
    (splitFiniteRates m r δ) t B D U S F y0 a b z H
    hk hxcurve hu hs hf hb hq
    (by simpa only [splitChartState_eq_reconstruct] using hET)
    (by simpa only [splitChartState_eq_reconstruct] using hFT)
    (by simpa only [splitChartState_eq_reconstruct] using hST)
    hH
  change (-1 : ℝ)^(m+1) *
    (sourceAugmentedCurrentMatrix (splitFiniteRates m r δ)
      (splitChartState m r δ y0)).det < 0 at hcurve
  rw [hchart] at hcurve
  exact hcurve

end
end PhosphorylationStableCapacity
