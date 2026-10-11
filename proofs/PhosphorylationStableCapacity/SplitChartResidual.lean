module
public import proofs.PhosphorylationStableCapacity.SplitDeterminantTransfer
public import proofs.PhosphorylationSharpness.PublicationAlgebra

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section

open PhosphorylationSharpness

/-- The substrate-total residual after solving the two enzyme-total
equations, written in the manuscript's regular scalar chart. -/
def chartSubstrateResidual (x v ell : ℝ) : ℝ :=
  (1 + ratio x) *
    (v / (ratio x * ell) - 2 * ell / (ell + v))

/-- The regular chart's substrate residual is a signed multiple of its
factor that vanishes at a prescribed equilibrium. -/
theorem chartSubstrateResidual_factor (x v ell : ℝ)
    (hx : 1 < x) (hell : ell ≠ 0) (hellv : ell + v ≠ 0) :
    chartSubstrateResidual x v ell =
      -2 * (1 + ratio x) *
        (ell + 2*v/(x+1)) / (ell*(ell+v)) *
          (ell - 2*v/(x-1)) := by
  have hu : ratio x ≠ 0 := ne_of_gt (ratio_pos hx)
  have hx1 : x - 1 ≠ 0 := by linarith
  have hx2 : x + 1 ≠ 0 := by linarith
  have hnum := residual_factorization x v ell hx
  unfold chartSubstrateResidual
  calc
    (1 + ratio x) *
        (v / (ratio x * ell) - 2 * ell / (ell + v)) =
      (1 + ratio x) *
        (v*(ell+v)-2*ratio x*ell^2) /
          (ratio x*ell*(ell+v)) := by
            field_simp
    _ = -2 * (1 + ratio x) *
        (ell + 2*v/(x+1)) / (ell*(ell+v)) *
          (ell - 2*v/(x-1)) := by
            rw [hnum]
            field_simp

theorem chart_vanishing_factor_eq_conversion
    (x r b d : ℝ) (hx : 1 < x) (hd : d ≠ 0) :
    (b/d-r) - 2*(r-ratio x)/(x-1) =
      ((x-1)*(b-r*d)-2*(r-ratio x)*d)/((x-1)*d) := by
  have hx1 : x-1 ≠ 0 := by linarith
  field_simp

def splitChartResidual (m : ℕ) (r δ x : ℝ) : ℝ :=
  let u := ratio x
  let b := (splitRawB m r δ).eval u
  let d := (splitRawD m r δ).eval u
  chartSubstrateResidual x (r-u) (b/d-r)

def chartConversionMultiplier (x v ell d : ℝ) : ℝ :=
  (-2 * (1+ratio x) * (ell+2*v/(x+1)) /
    (ell*(ell+v))) / ((x-1)*d)

theorem chartConversionMultiplier_neg (x v ell d : ℝ)
    (hx : 1 < x) (hv : 0 < v) (hell : 0 < ell) (hd : 0 < d) :
    chartConversionMultiplier x v ell d < 0 := by
  have hu : 0 < ratio x := ratio_pos hx
  have hxp : 0 < x+1 := by linarith
  have hsecond : 0 < ell+2*v/(x+1) := by
    apply add_pos hell
    exact div_pos (mul_pos (by norm_num) hv) hxp
  have hnum : -2 * (1+ratio x) * (ell+2*v/(x+1)) < 0 := by
    have hprod := mul_pos (by linarith : 0 < 1+ratio x) hsecond
    nlinarith
  have hden : 0 < ell*(ell+v) :=
    mul_pos hell (add_pos hell hv)
  exact div_neg_of_neg_of_pos
    (div_neg_of_neg_of_pos hnum hden)
    (mul_pos (sub_pos.mpr hx) hd)

/-- The physical scalar chart residual is an explicit rational multiplier
of the converted balance residual at every regular chart point. -/
theorem splitChartResidual_conversion_factor (m : ℕ) (r δ x : ℝ)
    (hx : 1 < x)
    (hd : (splitRawD m r δ).eval (ratio x) ≠ 0)
    (hell : (splitRawB m r δ).eval (ratio x) /
      (splitRawD m r δ).eval (ratio x) - r ≠ 0)
    (hellv : (splitRawB m r δ).eval (ratio x) /
      (splitRawD m r δ).eval (ratio x) - ratio x ≠ 0) :
    splitChartResidual m r δ x =
      -2 * (1+ratio x) *
        ((splitRawB m r δ).eval (ratio x) /
          (splitRawD m r δ).eval (ratio x) - r +
          2*(r-ratio x)/(x+1)) /
        (((splitRawB m r δ).eval (ratio x) /
          (splitRawD m r δ).eval (ratio x) - r) *
         ((splitRawB m r δ).eval (ratio x) /
          (splitRawD m r δ).eval (ratio x) - ratio x)) *
        (splitConversionResidual m r δ x /
          ((x-1)*(splitRawD m r δ).eval (ratio x))) := by
  unfold splitChartResidual
  dsimp only
  rw [chartSubstrateResidual_factor x _ _ hx hell]
  · rw [chart_vanishing_factor_eq_conversion x r
      ((splitRawB m r δ).eval (ratio x))
      ((splitRawD m r δ).eval (ratio x)) hx hd]
    have heq : (splitRawB m r δ).eval (ratio x) /
        (splitRawD m r δ).eval (ratio x) - r + (r-ratio x) =
          (splitRawB m r δ).eval (ratio x) /
            (splitRawD m r δ).eval (ratio x) - ratio x := by ring
    rw [heq]
    unfold splitConversionResidual
    rfl
  · convert hellv using 1
    ring

theorem splitChartResidual_eq_multiplier_mul (m : ℕ) (r δ x : ℝ)
    (hx : 1 < x)
    (hd : (splitRawD m r δ).eval (ratio x) ≠ 0)
    (hell : (splitRawB m r δ).eval (ratio x) /
      (splitRawD m r δ).eval (ratio x) - r ≠ 0)
    (hellv : (splitRawB m r δ).eval (ratio x) /
      (splitRawD m r δ).eval (ratio x) - ratio x ≠ 0) :
    splitChartResidual m r δ x =
      chartConversionMultiplier x (r-ratio x)
        ((splitRawB m r δ).eval (ratio x) /
          (splitRawD m r δ).eval (ratio x) - r)
        ((splitRawD m r δ).eval (ratio x)) *
          splitConversionResidual m r δ x := by
  rw [splitChartResidual_conversion_factor m r δ x hx hd hell hellv]
  unfold chartConversionMultiplier
  ring

end
end PhosphorylationStableCapacity
