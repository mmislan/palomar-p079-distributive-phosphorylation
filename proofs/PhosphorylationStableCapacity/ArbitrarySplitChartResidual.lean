module
public import proofs.PhosphorylationStableCapacity.ArbitrarySplitConversion
public import proofs.PhosphorylationStableCapacity.SplitChartDerivative

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section

open PhosphorylationSharpness Polynomial Filter
open scoped Topology

/-- The physical substrate-total chart residual for arbitrary prescribed
root offsets. -/
def arbitrarySplitChartResidual (m : ℕ) (ξ : ℕ → ℝ)
    (r δ x : ℝ) : ℝ :=
  let u := ratio x
  let b := (arbitrarySplitRawB m ξ r δ).eval u
  let d := (arbitrarySplitRawD m ξ r δ).eval u
  chartSubstrateResidual x (r-u) (b/d-r)

theorem arbitrarySplitConversionResidual_at_root
    (m : ℕ) (ξ : ℕ → ℝ) (r δ : ℝ)
    (j : Fin (2*m+1)) :
    arbitrarySplitConversionResidual m ξ r δ
      (offsetSplitRoot ξ δ j.val) = 0 := by
  rw [arbitrarySplitConversionResidual_factor,
    arbitrarySplitScalarProduct_eq_prod_range]
  have hj : j.val ∈ Finset.range (2*m+1) := Finset.mem_range.mpr j.isLt
  rw [Finset.prod_eq_zero hj (by simp)]
  ring

theorem arbitrarySplitChartEll_eq_at_root
    (m : ℕ) (ξ : ℕ → ℝ) (r δ : ℝ)
    (j : Fin (2*m+1))
    (hx : 1 < offsetSplitRoot ξ δ j.val)
    (hd : (arbitrarySplitRawD m ξ r δ).eval
      (ratio (offsetSplitRoot ξ δ j.val)) ≠ 0) :
    (arbitrarySplitRawB m ξ r δ).eval
        (ratio (offsetSplitRoot ξ δ j.val)) /
      (arbitrarySplitRawD m ξ r δ).eval
        (ratio (offsetSplitRoot ξ δ j.val)) - r =
        2*(r-ratio (offsetSplitRoot ξ δ j.val)) /
          (offsetSplitRoot ξ δ j.val-1) := by
  let x := offsetSplitRoot ξ δ j.val
  let d := (arbitrarySplitRawD m ξ r δ).eval (ratio x)
  let b := (arbitrarySplitRawB m ξ r δ).eval (ratio x)
  have hzero := arbitrarySplitConversionResidual_at_root m ξ r δ j
  have hrel : (x-1)*(b-r*d) = 2*(r-ratio x)*d := by
    dsimp only [arbitrarySplitConversionResidual, x, b, d] at hzero ⊢
    linarith
  have hx1 : x-1 ≠ 0 := by linarith
  have hd' : d ≠ 0 := hd
  have hb : b-r*d = 2*(r-ratio x)*d/(x-1) := by
    apply (eq_div_iff hx1).2
    linear_combination hrel
  calc
    b/d-r = (b-r*d)/d := by field_simp [hd']
    _ = (2*(r-ratio x)*d/(x-1))/d := by rw [hb]
    _ = 2*(r-ratio x)/(x-1) := by field_simp [hd', hx1]

theorem arbitrarySplitChartResidual_eq_multiplier_mul
    (m : ℕ) (ξ : ℕ → ℝ) (r δ x : ℝ)
    (hx : 1 < x)
    (hd : (arbitrarySplitRawD m ξ r δ).eval (ratio x) ≠ 0)
    (hell : (arbitrarySplitRawB m ξ r δ).eval (ratio x) /
      (arbitrarySplitRawD m ξ r δ).eval (ratio x) - r ≠ 0)
    (hellv : (arbitrarySplitRawB m ξ r δ).eval (ratio x) /
      (arbitrarySplitRawD m ξ r δ).eval (ratio x) - ratio x ≠ 0) :
    arbitrarySplitChartResidual m ξ r δ x =
      chartConversionMultiplier x (r-ratio x)
        ((arbitrarySplitRawB m ξ r δ).eval (ratio x) /
          (arbitrarySplitRawD m ξ r δ).eval (ratio x) - r)
        ((arbitrarySplitRawD m ξ r δ).eval (ratio x)) *
          arbitrarySplitConversionResidual m ξ r δ x := by
  unfold arbitrarySplitChartResidual
  dsimp only
  rw [chartSubstrateResidual_factor x _ _ hx hell]
  · rw [chart_vanishing_factor_eq_conversion x r
      ((arbitrarySplitRawB m ξ r δ).eval (ratio x))
      ((arbitrarySplitRawD m ξ r δ).eval (ratio x)) hx hd]
    have heq : (arbitrarySplitRawB m ξ r δ).eval (ratio x) /
        (arbitrarySplitRawD m ξ r δ).eval (ratio x) - r +
          (r-ratio x) =
        (arbitrarySplitRawB m ξ r δ).eval (ratio x) /
          (arbitrarySplitRawD m ξ r δ).eval (ratio x) - ratio x := by ring
    rw [heq]
    unfold chartConversionMultiplier arbitrarySplitConversionResidual
    ring
  · convert hellv using 1
    ring

end
end PhosphorylationStableCapacity
