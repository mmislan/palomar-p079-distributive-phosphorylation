module
public import proofs.PhosphorylationStableCapacity.ArbitrarySplitChartResidual

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section

open PhosphorylationSharpness Polynomial Filter
open scoped Topology

theorem arbitrarySplitChartResidual_eventually_conversion
    (m : ℕ) (ξ : ℕ → ℝ) (r δ : ℝ)
    (j : Fin (2*m+1))
    (hD : DensePositive (arbitrarySplitRawD m ξ r δ) m)
    (hx : 1 < offsetSplitRoot ξ δ j.val)
    (hv : 0 < r-ratio (offsetSplitRoot ξ δ j.val)) :
    (fun y => arbitrarySplitChartResidual m ξ r δ y) =ᶠ[𝓝 (offsetSplitRoot ξ δ j.val)]
      (fun y => chartConversionMultiplier y (r-ratio y)
        ((arbitrarySplitRawB m ξ r δ).eval (ratio y) /
          (arbitrarySplitRawD m ξ r δ).eval (ratio y)-r)
        ((arbitrarySplitRawD m ξ r δ).eval (ratio y)) *
          arbitrarySplitConversionResidual m ξ r δ y) := by
  let x0 := offsetSplitRoot ξ δ j.val
  let D := arbitrarySplitRawD m ξ r δ
  let B := arbitrarySplitRawB m ξ r δ
  have hd0 : 0 < D.eval (ratio x0) := hD.eval_pos (ratio_pos hx)
  have hell0 : 0 < B.eval (ratio x0)/D.eval (ratio x0)-r := by
    rw [arbitrarySplitChartEll_eq_at_root m ξ r δ j hx (ne_of_gt hd0)]
    exact div_pos (mul_pos (by norm_num) hv) (sub_pos.mpr hx)
  have hratio : ContinuousAt ratio x0 := by
    unfold ratio
    fun_prop
  have hdc : ContinuousAt (fun y : ℝ => D.eval (ratio y)) x0 :=
    D.continuousAt.comp hratio
  have hbc : ContinuousAt (fun y : ℝ => B.eval (ratio y)) x0 :=
    B.continuousAt.comp hratio
  have hec : ContinuousAt
      (fun y : ℝ => B.eval (ratio y)/D.eval (ratio y)-r) x0 :=
    (hbc.div hdc (ne_of_gt hd0)).sub continuousAt_const
  have hvc : ContinuousAt (fun y : ℝ => r-ratio y) x0 :=
    continuousAt_const.sub hratio
  have hnearx : ∀ᶠ y in 𝓝 x0, 1 < y := Ioi_mem_nhds hx
  have hneard : ∀ᶠ y in 𝓝 x0, 0 < D.eval (ratio y) :=
    hdc.eventually (Ioi_mem_nhds hd0)
  have hnearv : ∀ᶠ y in 𝓝 x0, 0 < r-ratio y :=
    hvc.eventually (Ioi_mem_nhds hv)
  have hnearell : ∀ᶠ y in 𝓝 x0,
      0 < B.eval (ratio y)/D.eval (ratio y)-r :=
    hec.eventually (Ioi_mem_nhds hell0)
  filter_upwards [hnearx, hneard, hnearv, hnearell]
    with y hyx hyd hyv hyell
  have hellv : B.eval (ratio y)/D.eval (ratio y)-ratio y ≠ 0 := by
    have : 0 < B.eval (ratio y)/D.eval (ratio y)-ratio y := by
      linarith
    exact ne_of_gt this
  exact arbitrarySplitChartResidual_eq_multiplier_mul m ξ r δ y hyx
    (ne_of_gt hyd) (ne_of_gt hyell) hellv

theorem arbitrarySplitChartMultiplier_differentiableAt
    (m : ℕ) (ξ : ℕ → ℝ) (r δ x : ℝ)
    (hx : 1 < x)
    (hd : 0 < (arbitrarySplitRawD m ξ r δ).eval (ratio x))
    (hv : 0 < r-ratio x)
    (hell : 0 < (arbitrarySplitRawB m ξ r δ).eval (ratio x) /
      (arbitrarySplitRawD m ξ r δ).eval (ratio x)-r) :
    DifferentiableAt ℝ
      (fun y => chartConversionMultiplier y (r-ratio y)
        ((arbitrarySplitRawB m ξ r δ).eval (ratio y) /
          (arbitrarySplitRawD m ξ r δ).eval (ratio y)-r)
        ((arbitrarySplitRawD m ξ r δ).eval (ratio y))) x := by
  have hxp : 0 < x+1 := by linarith
  have hxm : 0 < x-1 := by linarith
  have hellv : 0 < (arbitrarySplitRawB m ξ r δ).eval (ratio x) /
      (arbitrarySplitRawD m ξ r δ).eval (ratio x)-ratio x := by linarith
  unfold chartConversionMultiplier ratio
  fun_prop (disch := positivity)

/-- The physical chart slope has the exact arbitrary-root gap factor. -/
theorem arbitrarySplitChartResidual_deriv_at_root
    (m : ℕ) (ξ : ℕ → ℝ) (r δ : ℝ)
    (j : Fin (2*m+1))
    (hD : DensePositive (arbitrarySplitRawD m ξ r δ) m)
    (hx : 1 < offsetSplitRoot ξ δ j.val)
    (hv : 0 < r-ratio (offsetSplitRoot ξ δ j.val)) :
    deriv (fun y => arbitrarySplitChartResidual m ξ r δ y)
      (offsetSplitRoot ξ δ j.val) =
      chartConversionMultiplier (offsetSplitRoot ξ δ j.val)
        (r-ratio (offsetSplitRoot ξ δ j.val))
        ((arbitrarySplitRawB m ξ r δ).eval
            (ratio (offsetSplitRoot ξ δ j.val)) /
          (arbitrarySplitRawD m ξ r δ).eval
            (ratio (offsetSplitRoot ξ δ j.val))-r)
        ((arbitrarySplitRawD m ξ r δ).eval
          (ratio (offsetSplitRoot ξ δ j.val))) *
      ((4*r*(arbitrarySplitPair m ξ δ).1.eval r+
        (offsetSplitRoot ξ δ j.val-1)*
          (arbitrarySplitPair m ξ δ).2.eval r) *
        (δ^(2*m) *
          ∏ i ∈ (Finset.range (2*m+1)).erase j.val,
            (ξ j.val-ξ i))) := by
  let x := offsetSplitRoot ξ δ j.val
  let D := arbitrarySplitRawD m ξ r δ
  let B := arbitrarySplitRawB m ξ r δ
  let M : ℝ → ℝ := fun y => chartConversionMultiplier y (r-ratio y)
    (B.eval (ratio y)/D.eval (ratio y)-r) (D.eval (ratio y))
  let R : ℝ → ℝ := fun y => arbitrarySplitConversionResidual m ξ r δ y
  have hd : 0 < D.eval (ratio x) := hD.eval_pos (ratio_pos hx)
  have hell : 0 < B.eval (ratio x)/D.eval (ratio x)-r := by
    rw [arbitrarySplitChartEll_eq_at_root m ξ r δ j hx (ne_of_gt hd)]
    exact div_pos (mul_pos (by norm_num) hv) (sub_pos.mpr hx)
  have hM : DifferentiableAt ℝ M x :=
    arbitrarySplitChartMultiplier_differentiableAt m ξ r δ x hx hd hv hell
  have hR : DifferentiableAt ℝ R x := by
    unfold R arbitrarySplitConversionResidual ratio
    fun_prop
  have hzero : R x = 0 :=
    arbitrarySplitConversionResidual_at_root m ξ r δ j
  have heq : (fun y => arbitrarySplitChartResidual m ξ r δ y) =ᶠ[𝓝 x]
      (fun y => M y*R y) :=
    arbitrarySplitChartResidual_eventually_conversion
      m ξ r δ j hD hx hv
  rw [heq.deriv_eq]
  change deriv (M*R) x = _
  rw [deriv_mul hM hR, hzero, mul_zero, zero_add,
    arbitrarySplitConversionResidual_deriv_at_root m j.val ξ r δ j.isLt]

end
end PhosphorylationStableCapacity
