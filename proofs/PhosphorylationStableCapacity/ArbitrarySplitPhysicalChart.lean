module
public import proofs.PhosphorylationStableCapacity.ArbitrarySplitPhysicalPrefactor
public import proofs.PhosphorylationStableCapacity.ArbitrarySplitEvaluationDifferentiability

@[expose] public section
set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

namespace PhosphorylationStableCapacity

noncomputable section

open PhosphorylationSharpness Polynomial

private theorem chartConversionMultiplier_params_differentiableAt
    (y v ell d : ℝ → ℝ)
    (hy : DifferentiableAt ℝ y 0)
    (hv : DifferentiableAt ℝ v 0)
    (hell : DifferentiableAt ℝ ell 0)
    (hd : DifferentiableAt ℝ d 0)
    (hypos : 1 < y 0)
    (hvpos : 0 < v 0)
    (hellpos : 0 < ell 0)
    (hdpos : 0 < d 0) :
    DifferentiableAt ℝ
      (fun δ => chartConversionMultiplier (y δ) (v δ) (ell δ) (d δ)) 0 := by
  unfold chartConversionMultiplier ratio
  fun_prop (disch := positivity)

theorem arbitrarySplitPhysicalChart_differentiableAt
    (m : ℕ) (ξ : ℕ → ℝ) (r : ℝ)
    (hr : 1 < r)
    (hD₀ : DensePositive (coalescedRawD (m+1) r) (m+1))
    (j : Fin (2*(m+1)+1)) :
    DifferentiableAt ℝ (fun δ =>
      let y := offsetSplitRoot ξ δ j.val
      let u := ratio y
      let d := (arbitrarySplitRawD (m+1) ξ r δ).eval u
      let ell := (arbitrarySplitRawB (m+1) ξ r δ).eval u / d - r
      chartConversionMultiplier y (r-u) ell d) 0 := by
  let y : ℝ → ℝ := fun δ => offsetSplitRoot ξ δ j.val
  let u : ℝ → ℝ := fun δ => ratio (y δ)
  let d : ℝ → ℝ := fun δ =>
    (arbitrarySplitRawD (m+1) ξ r δ).eval (u δ)
  let b : ℝ → ℝ := fun δ =>
    (arbitrarySplitRawB (m+1) ξ r δ).eval (u δ)
  let v : ℝ → ℝ := fun δ => r-u δ
  let ell : ℝ → ℝ := fun δ => b δ / d δ-r
  have hr0 : r ≠ 0 := by linarith
  have hy : Differentiable ℝ y := by
    dsimp [y, offsetSplitRoot]
    fun_prop
  have hu : Differentiable ℝ u := by
    dsimp [u, y, ratio, offsetSplitRoot]
    fun_prop
  have hd : Differentiable ℝ d :=
    arbitrarySplitRawD_eval_differentiable (m+1) ξ r hr0 u hu
  have hb : Differentiable ℝ b :=
    arbitrarySplitRawB_eval_differentiable (m+1) ξ r hr0 u hu
  have hypos : 1 < y 0 := by norm_num [y, offsetSplitRoot]
  have hvpos : 0 < v 0 := by
    norm_num [v, u, y, ratio, offsetSplitRoot]
    linarith
  have hu0 : u 0 = 1 := by
    norm_num [u, y, ratio, offsetSplitRoot]
  have hdpos : 0 < d 0 := by
    simpa [d, hu0, arbitrarySplitRawD, coalescedRawD,
      arbitrarySplitPair_zero_eq_coalesced] using
      hD₀.eval_pos (by norm_num : 0 < (1 : ℝ))
  have hell0 : ell 0 = 2*v 0/(y 0-1) := by
    exact arbitrarySplitChartEll_eq_at_root (m+1) ξ r 0 j hypos
      (ne_of_gt hdpos)
  have hellpos : 0 < ell 0 := by
    rw [hell0]
    exact div_pos (mul_pos (by norm_num) hvpos) (sub_pos.mpr hypos)
  have hv : DifferentiableAt ℝ v 0 := by
    exact (differentiableAt_const _).sub hu.differentiableAt
  have hell : DifferentiableAt ℝ ell 0 := by
    exact (hb.differentiableAt.div hd.differentiableAt
      (ne_of_gt hdpos)).sub (differentiableAt_const _)
  change DifferentiableAt ℝ
    (fun δ => chartConversionMultiplier (y δ) (v δ) (ell δ) (d δ)) 0
  exact chartConversionMultiplier_params_differentiableAt y v ell d
    hy.differentiableAt hv hell hd.differentiableAt
    hypos hvpos hellpos hdpos

theorem arbitrarySplitPhysicalPrefactor_differentiableAt
    (m : ℕ) (ξ : ℕ → ℝ) (r τ ε : ℝ)
    (hr : 1 < r)
    (hD₀ : DensePositive (coalescedRawD (m+1) r) (m+1))
    (hB₀ : DensePositive (coalescedRawB (m+1) r) (m+1))
    (j : Fin (2*(m+1)+1))
    (hstate0 :
      (arbitrarySplitFiniteState (m+1) ξ r 0 j).S 0 *
      (arbitrarySplitFiniteState (m+1) ξ r 0 j).E *
      (arbitrarySplitFiniteState (m+1) ξ r 0 j).F ≠ 0) :
    DifferentiableAt ℝ
      (arbitrarySplitPhysicalPrefactor m ξ r τ ε j) 0 := by
  apply arbitrarySplitPhysicalPrefactor_differentiableAt_of_chart
    m ξ r τ ε (by linarith) hD₀ hB₀ j hstate0
  exact arbitrarySplitPhysicalChart_differentiableAt m ξ r hr hD₀ j

end
end PhosphorylationStableCapacity
