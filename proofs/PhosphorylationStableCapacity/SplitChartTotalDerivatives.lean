module
public import proofs.PhosphorylationStableCapacity.SplitChartTangent

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section
open PhosphorylationSharpness Polynomial Filter
open scoped Topology

/-- At a prescribed split root the actual reconstructed chart keeps
both enzyme totals stationary and its substrate-total derivative is
the already analyzed regular scalar residual derivative. -/
theorem splitChartState_total_derivatives_at_root
    (m : ℕ) (r δ : ℝ) (j : Fin (2*m+1))
    (hD : DensePositive (splitRawD m r δ) m)
    (hB : DensePositive (splitRawB m r δ) m)
    (hx : 1 < splitRoot δ j.val)
    (hv : 0 < r-ratio (splitRoot δ j.val)) :
    HasDerivAt (fun y => totalE (splitChartState m r δ y)) 0
        (splitRoot δ j.val) ∧
      HasDerivAt (fun y => totalF (splitChartState m r δ y)) 0
        (splitRoot δ j.val) ∧
      HasDerivAt (fun y => totalS (splitChartState m r δ y))
        (deriv (fun y => splitChartResidual m r δ y)
          (splitRoot δ j.val)) (splitRoot δ j.val) := by
  let y0 := splitRoot δ j.val
  let D := splitRawD m r δ
  let B := splitRawB m r δ
  let u := fun y : ℝ => ratio y
  let d := fun y : ℝ => D.eval (u y)
  let ell := fun y : ℝ => B.eval (u y)/d y-r
  have hu0 : 0 < u y0 := ratio_pos hx
  have hd0 : 0 < d y0 := hD.eval_pos hu0
  have hell0 : 0 < ell y0 := by
    dsimp [ell, d, u, y0]
    rw [splitChartEll_eq_at_root m r δ j hx (ne_of_gt hd0)]
    exact div_pos (mul_pos (by norm_num) hv) (sub_pos.mpr hx)
  have hellv0 : 0 < ell y0 + (r-u y0) := by
    linarith
  have huc : ContinuousAt u y0 := by
    dsimp [u, ratio]
    fun_prop
  have hdc : ContinuousAt d y0 := D.continuousAt.comp huc
  have hec : ContinuousAt ell y0 :=
    (B.continuousAt.comp huc).div hdc (ne_of_gt hd0) |>.sub continuousAt_const
  have hvc : ContinuousAt (fun y : ℝ => r-u y) y0 :=
    continuousAt_const.sub huc
  have hnearx : ∀ᶠ y in 𝓝 y0, 1 < y := Ioi_mem_nhds hx
  have hneard : ∀ᶠ y in 𝓝 y0, 0 < d y :=
    hdc.eventually (Ioi_mem_nhds hd0)
  have hnearell : ∀ᶠ y in 𝓝 y0, 0 < ell y :=
    hec.eventually (Ioi_mem_nhds hell0)
  have hnearellv : ∀ᶠ y in 𝓝 y0, 0 < ell y+(r-u y) :=
    (hec.add hvc).eventually (Ioi_mem_nhds hellv0)
  have htot : ∀ᶠ y in 𝓝 y0,
      totalE (splitChartState m r δ y) = 2*r ∧
      totalF (splitChartState m r δ y) = 2 ∧
      totalS (splitChartState m r δ y)-2*(r+1) =
        splitChartResidual m r δ y := by
    filter_upwards [hnearx, hneard, hnearell, hnearellv]
      with y hyx hyd hyell hyellv
    exact splitChartState_totals m r δ y hyx hD hB
      (ne_of_gt hyell) (by
        have : ell y+(r-u y) = B.eval (u y)/d y-u y := by
          dsimp [ell]
          ring
        rw [this] at hyellv
        exact ne_of_gt hyellv)
  have hEeq : (fun y => totalE (splitChartState m r δ y)) =ᶠ[𝓝 y0]
      (fun _ : ℝ => 2*r) := by
    filter_upwards [htot] with y hy
    exact hy.1
  have hFeq : (fun y => totalF (splitChartState m r δ y)) =ᶠ[𝓝 y0]
      (fun _ : ℝ => 2) := by
    filter_upwards [htot] with y hy
    exact hy.2.1
  have hSeq : (fun y => totalS (splitChartState m r δ y)) =ᶠ[𝓝 y0]
      (fun y => splitChartResidual m r δ y+2*(r+1)) := by
    filter_upwards [htot] with y hy
    linarith [hy.2.2]
  have hM : DifferentiableAt ℝ
      (fun y => chartConversionMultiplier y (r-ratio y)
        (B.eval (ratio y)/D.eval (ratio y)-r)
        (D.eval (ratio y))) y0 := by
    exact splitChartMultiplier_differentiableAt m r δ y0 hx hd0 hv hell0
  have hR : DifferentiableAt ℝ
      (fun y => splitConversionResidual m r δ y) y0 :=
    (splitConversionResidual_differentiable m r δ).differentiableAt
  have hresEq := splitChartResidual_eventually_conversion
    m r δ j hD hx hv
  have hres : DifferentiableAt ℝ
      (fun y => splitChartResidual m r δ y) y0 := by
    have hprod := hM.mul hR
    exact hprod.congr_of_eventuallyEq hresEq
  refine ⟨(hasDerivAt_const y0 (2*r)).congr_of_eventuallyEq hEeq,
    (hasDerivAt_const y0 (2 : ℝ)).congr_of_eventuallyEq hFeq, ?_⟩
  have h := hres.hasDerivAt.add_const (2*(r+1))
  exact h.congr_of_eventuallyEq hSeq

end
end PhosphorylationStableCapacity
