module
public import proofs.PhosphorylationStableCapacity.SplitChartState
public import Mathlib.Analysis.Calculus.Deriv.Polynomial

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section

open PhosphorylationSharpness Polynomial Filter
open scoped Topology

/-- Near a prescribed positive root the regular substrate-total residual
is exactly the negative chart multiplier times the converted balance gap. -/
theorem splitChartResidual_eventually_conversion (m : ℕ) (r δ : ℝ)
    (j : Fin (2*m+1))
    (hD : DensePositive (splitRawD m r δ) m)
    (hx : 1 < splitRoot δ j.val)
    (hv : 0 < r-ratio (splitRoot δ j.val)) :
    (fun y => splitChartResidual m r δ y) =ᶠ[𝓝 (splitRoot δ j.val)]
      (fun y => chartConversionMultiplier y (r-ratio y)
        ((splitRawB m r δ).eval (ratio y) /
          (splitRawD m r δ).eval (ratio y)-r)
        ((splitRawD m r δ).eval (ratio y)) *
          splitConversionResidual m r δ y) := by
  let x0 := splitRoot δ j.val
  let D := splitRawD m r δ
  let B := splitRawB m r δ
  have hd0 : 0 < D.eval (ratio x0) := hD.eval_pos (ratio_pos hx)
  have hell0 : 0 < B.eval (ratio x0)/D.eval (ratio x0)-r := by
    rw [splitChartEll_eq_at_root m r δ j hx (ne_of_gt hd0)]
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
  exact splitChartResidual_eq_multiplier_mul m r δ y hyx
    (ne_of_gt hyd) (ne_of_gt hyell) hellv

theorem splitChartMultiplier_differentiableAt (m : ℕ) (r δ x : ℝ)
    (hx : 1 < x)
    (hd : 0 < (splitRawD m r δ).eval (ratio x))
    (hv : 0 < r-ratio x)
    (hell : 0 < (splitRawB m r δ).eval (ratio x) /
      (splitRawD m r δ).eval (ratio x)-r) :
    DifferentiableAt ℝ
      (fun y => chartConversionMultiplier y (r-ratio y)
        ((splitRawB m r δ).eval (ratio y) /
          (splitRawD m r δ).eval (ratio y)-r)
        ((splitRawD m r δ).eval (ratio y))) x := by
  have hxp : 0 < x+1 := by linarith
  have hxm : 0 < x-1 := by linarith
  have hellv : 0 < (splitRawB m r δ).eval (ratio x) /
      (splitRawD m r δ).eval (ratio x)-ratio x := by linarith
  unfold chartConversionMultiplier ratio
  fun_prop (disch := positivity)

/-- At a root the derivative of the physical substrate-total residual is
the converted balance derivative times the strictly negative chart factor. -/
theorem splitChartResidual_deriv_at_root (m : ℕ) (r δ : ℝ)
    (j : Fin (2*m+1))
    (hD : DensePositive (splitRawD m r δ) m)
    (hx : 1 < splitRoot δ j.val)
    (hv : 0 < r-ratio (splitRoot δ j.val)) :
    deriv (fun y => splitChartResidual m r δ y)
      (splitRoot δ j.val) =
      chartConversionMultiplier (splitRoot δ j.val)
        (r-ratio (splitRoot δ j.val))
        ((splitRawB m r δ).eval (ratio (splitRoot δ j.val)) /
          (splitRawD m r δ).eval (ratio (splitRoot δ j.val))-r)
        ((splitRawD m r δ).eval (ratio (splitRoot δ j.val))) *
      deriv (fun y => splitConversionResidual m r δ y)
        (splitRoot δ j.val) := by
  let x := splitRoot δ j.val
  let D := splitRawD m r δ
  let B := splitRawB m r δ
  let M : ℝ → ℝ := fun y => chartConversionMultiplier y (r-ratio y)
    (B.eval (ratio y)/D.eval (ratio y)-r) (D.eval (ratio y))
  let R : ℝ → ℝ := fun y => splitConversionResidual m r δ y
  have hd : 0 < D.eval (ratio x) := hD.eval_pos (ratio_pos hx)
  have hell : 0 < B.eval (ratio x)/D.eval (ratio x)-r := by
    rw [splitChartEll_eq_at_root m r δ j hx (ne_of_gt hd)]
    exact div_pos (mul_pos (by norm_num) hv) (sub_pos.mpr hx)
  have hM : DifferentiableAt ℝ M x :=
    splitChartMultiplier_differentiableAt m r δ x hx hd hv hell
  have hR : DifferentiableAt ℝ R x :=
    (splitConversionResidual_differentiable m r δ).differentiableAt
  have hzero : R x = 0 :=
    splitConversionResidual_at_root m j.val r δ (by omega)
  have heq : (fun y => splitChartResidual m r δ y) =ᶠ[𝓝 x]
      (fun y => M y*R y) :=
    splitChartResidual_eventually_conversion m r δ j hD hx hv
  rw [heq.deriv_eq]
  change deriv (M*R) x = M x * deriv R x
  rw [deriv_mul hM hR]
  simp [hzero]

theorem splitChartResidual_deriv_alternates (m : ℕ) (r δ : ℝ)
    (j : Fin (2*m+1))
    (hr : 0 < r) (hδ : 0 < δ)
    (hD : DensePositive (splitRawD m r δ) m)
    (hv : 0 < r-ratio (splitRoot δ j.val)) :
    (Even j.val → deriv (fun y => splitChartResidual m r δ y)
      (splitRoot δ j.val) < 0) ∧
    (Odd j.val → 0 < deriv (fun y => splitChartResidual m r δ y)
      (splitRoot δ j.val)) := by
  let x := splitRoot δ j.val
  have hx : 1 < x := by
    have hnonneg : 0 ≤ δ*(j.val:ℝ) :=
      mul_nonneg hδ.le (Nat.cast_nonneg _)
    dsimp [x, splitRoot]
    linarith
  have hd : 0 < (splitRawD m r δ).eval (ratio x) :=
    hD.eval_pos (ratio_pos hx)
  have hell : 0 < (splitRawB m r δ).eval (ratio x) /
      (splitRawD m r δ).eval (ratio x)-r := by
    rw [splitChartEll_eq_at_root m r δ j hx (ne_of_gt hd)]
    exact div_pos (mul_pos (by norm_num) hv) (sub_pos.mpr hx)
  have hM : chartConversionMultiplier x (r-ratio x)
      ((splitRawB m r δ).eval (ratio x) /
        (splitRawD m r δ).eval (ratio x)-r)
      ((splitRawD m r δ).eval (ratio x)) < 0 :=
    chartConversionMultiplier_neg x (r-ratio x)
      ((splitRawB m r δ).eval (ratio x) /
        (splitRawD m r δ).eval (ratio x)-r)
      ((splitRawD m r δ).eval (ratio x)) hx hv hell hd
  have hR := splitConversionResidual_deriv_alternates m j.val hr hδ
    (by omega : j.val < 2*m+1)
  rw [splitChartResidual_deriv_at_root m r δ j hD hx hv]
  exact ⟨fun he => mul_neg_of_neg_of_pos hM (hR.1 he),
    fun ho => mul_pos_of_neg_of_neg hM (hR.2 ho)⟩

end
end PhosphorylationStableCapacity
