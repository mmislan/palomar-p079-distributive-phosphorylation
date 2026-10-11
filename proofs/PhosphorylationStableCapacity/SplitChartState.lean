module
public import proofs.PhosphorylationStableCapacity.SplitClearedChart

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section

open PhosphorylationSharpness Polynomial
open Filter
open scoped Topology

def chartS (u r ell d : ℝ) : ℝ :=
  (r-u)/(u*d*ell)

def chartF (u r ell : ℝ) : ℝ :=
  2*ell/(ell+(r-u))

theorem chartS_pos {u r ell d : ℝ}
    (hu : 0 < u) (hd : 0 < d) (hell : 0 < ell)
    (hv : 0 < r-u) : 0 < chartS u r ell d := by
  unfold chartS
  exact div_pos hv (mul_pos (mul_pos hu hd) hell)

theorem chartF_pos {u r ell : ℝ}
    (hell : 0 < ell) (hv : 0 < r-u) :
    0 < chartF u r ell := by
  unfold chartF
  exact div_pos (mul_pos (by norm_num) hell) (add_pos hell hv)

/-- Solving both enzyme totals leaves exactly the stated substrate-total
residual, before any source polynomial is substituted. -/
theorem chart_totals_algebra (u r ell d : ℝ)
    (hu : u ≠ 0) (hd : d ≠ 0) (hell : ell ≠ 0)
    (hellv : ell+(r-u) ≠ 0) :
    let b := d*(r+ell)
    let s := chartS u r ell d
    let f := chartF u r ell
    u*f*(1+s*b)=2*r ∧
    f*(1+s*u*d)=2 ∧
    s*(1+u)*d+u*s*f*(b+d)-2*(r+1) =
      (1+u)*((r-u)/(u*ell)-2*ell/(ell+(r-u))) := by
  dsimp [chartS, chartF]
  constructor
  · field_simp
    ring
  · constructor
    · field_simp
    · field_simp
      ring

/-- The actual reconstructed source states along the two-enzyme-total
constraint curve, at arbitrary regular `x`. -/
def splitChartState (m : ℕ) (r δ x : ℝ) : State (m+1) :=
  let D := splitRawD m r δ
  let B := splitRawB m r δ
  let u := ratio x
  let d := D.eval u
  let ell := B.eval u / d - r
  reconstruct
    (fun i : Fin (m+2) => (((1+X)*D : ℝ[X]).coeff i))
    (fun i : Fin (m+1) => B.coeff i)
    (fun i : Fin (m+1) => D.coeff i)
    u (chartS u r ell d) (chartF u r ell)

theorem splitChartState_positive (m : ℕ) (r δ x : ℝ)
    (hx : 1 < x)
    (hD : DensePositive (splitRawD m r δ) m)
    (hB : DensePositive (splitRawB m r δ) m)
    (hv : 0 < r-ratio x)
    (hell : 0 < (splitRawB m r δ).eval (ratio x) /
      (splitRawD m r δ).eval (ratio x) - r) :
    (splitChartState m r δ x).Positive := by
  let D := splitRawD m r δ
  let B := splitRawB m r δ
  let A : ℝ[X] := (1+X)*D
  let u := ratio x
  let d := D.eval u
  let ell := B.eval u/d-r
  have hA : DensePositive A (m+1) := dense_inventory_product hD
  have hu : 0 < u := ratio_pos hx
  have hd : 0 < d := hD.eval_pos hu
  have hs : 0 < chartS u r ell d := chartS_pos hu hd hell hv
  have hf : 0 < chartF u r ell := chartF_pos hell hv
  have hpos := reconstruct_positive
    (fun i : Fin (m+2) => A.coeff i)
    (fun i : Fin (m+1) => B.coeff i)
    (fun i : Fin (m+1) => D.coeff i)
    (fun i => hA.1 i (by omega))
    (fun i => hB.1 i (by omega))
    (fun i => hD.1 i (by omega)) hu hs hf
  simpa only [splitChartState, A, B, D, u, d, ell] using hpos

theorem splitChartState_totals (m : ℕ) (r δ x : ℝ)
    (hx : 1 < x)
    (hD : DensePositive (splitRawD m r δ) m)
    (hB : DensePositive (splitRawB m r δ) m)
    (hell : (splitRawB m r δ).eval (ratio x) /
      (splitRawD m r δ).eval (ratio x) - r ≠ 0)
    (hellv : (splitRawB m r δ).eval (ratio x) /
      (splitRawD m r δ).eval (ratio x) - ratio x ≠ 0) :
    totalE (splitChartState m r δ x) = 2*r ∧
      totalF (splitChartState m r δ x) = 2 ∧
      totalS (splitChartState m r δ x) - 2*(r+1) =
        splitChartResidual m r δ x := by
  let D := splitRawD m r δ
  let B := splitRawB m r δ
  let A : ℝ[X] := (1+X)*D
  let u := ratio x
  let d := D.eval u
  let b := B.eval u
  let ell := b/d-r
  let s := chartS u r ell d
  let f := chartF u r ell
  have hu : u ≠ 0 := ne_of_gt (ratio_pos hx)
  have hd : d ≠ 0 := ne_of_gt (hD.eval_pos (ratio_pos hx))
  have hell' : ell ≠ 0 := hell
  have hellv' : ell+(r-u) ≠ 0 := by
    convert hellv using 1
    ring
  have hbd : b = d*(r+ell) := by
    dsimp [ell]
    field_simp
    ring
  have halg := chart_totals_algebra u r ell d hu hd hell' hellv'
  dsimp only at halg
  rw [← hbd] at halg
  have hA : DensePositive A (m+1) := dense_inventory_product hD
  have htot := reconstruct_totals
    (fun i : Fin (m+2) => A.coeff i)
    (fun i : Fin (m+1) => B.coeff i)
    (fun i : Fin (m+1) => D.coeff i) u s f
  rw [dense_inventory hB, dense_inventory hD, dense_inventory hA] at htot
  simp only [A, eval_mul, eval_add, eval_one, eval_X] at htot
  change totalE (splitChartState m r δ x) = 2*r ∧
    totalF (splitChartState m r δ x) = 2 ∧
    totalS (splitChartState m r δ x) - 2*(r+1) =
      splitChartResidual m r δ x
  refine ⟨htot.1.trans halg.1, htot.2.1.trans halg.2.1, ?_⟩
  change totalS (reconstruct
    (fun i : Fin (m+2) => (((1+X)*D : ℝ[X]).coeff i))
    (fun i : Fin (m+1) => B.coeff i)
    (fun i : Fin (m+1) => D.coeff i) u s f) - 2*(r+1) =
      splitChartResidual m r δ x
  rw [htot.2.2]
  calc
    s * ((1 + u) * eval u D) +
        u * s * f * (eval u (splitRawB m r δ) + eval u (splitRawD m r δ)) -
        2 * (r + 1) =
      chartS u r ell d * (1+u) * d +
        u * chartS u r ell d * chartF u r ell * (b+d) - 2*(r+1) := by
          dsimp only [s, f, b, d, D, B]
          ring
    _ = (1+u)*((r-u)/(u*ell)-2*ell/(ell+(r-u))) := halg.2.2
    _ = splitChartResidual m r δ x := rfl

/-- At a conversion root the enzyme-total chart specializes to the
explicit state used by the split source construction. -/
theorem chart_values_at_conversion_root (x r d ell : ℝ)
    (hx : 1 < x) (hd : d ≠ 0)
    (hv : r-ratio x ≠ 0)
    (hell : ell = 2*(r-ratio x)/(x-1)) :
    chartS (ratio x) r ell d = rootS x d ∧
      chartF (ratio x) r ell = rootF x := by
  have hx1 : x-1 ≠ 0 := by linarith
  have hx2 : x+1 ≠ 0 := by linarith
  constructor
  · rw [hell]
    unfold chartS rootS
    field_simp
  · rw [hell]
    let v := r-ratio x
    have hv' : v ≠ 0 := hv
    have hsum : 2*(r-ratio x)/(x-1)+(r-ratio x) ≠ 0 := by
      have heq : 2*(r-ratio x)/(x-1)+(r-ratio x) =
          (r-ratio x)*(x+1)/(x-1) := by
        field_simp
        ring
      rw [heq]
      exact div_ne_zero (mul_ne_zero hv hx2) hx1
    unfold chartF rootF
    change 2*(2*v/(x-1))/(2*v/(x-1)+v) = 4/(x+1)
    have hsum' : 2*v/(x-1)+v ≠ 0 := hsum
    field_simp [hx1, hx2, hv', hsum']
    ring_nf
    have hxp : 1+x ≠ 0 := by linarith
    calc
      x * (1+x)⁻¹ * 4 + (1+x)⁻¹ * 4 =
          (1+x)*(1+x)⁻¹*4 := by ring
      _ = 4 := by simp [hxp]

theorem splitChartEll_eq_at_root (m : ℕ) (r δ : ℝ)
    (j : Fin (2*m+1))
    (hx : 1 < splitRoot δ j.val)
    (hd : (splitRawD m r δ).eval (ratio (splitRoot δ j.val)) ≠ 0) :
    (splitRawB m r δ).eval (ratio (splitRoot δ j.val)) /
      (splitRawD m r δ).eval (ratio (splitRoot δ j.val)) - r =
        2*(r-ratio (splitRoot δ j.val))/(splitRoot δ j.val-1) := by
  let x := splitRoot δ j.val
  let d := (splitRawD m r δ).eval (ratio x)
  let b := (splitRawB m r δ).eval (ratio x)
  have hzero := splitConversionResidual_at_root m j.val r δ (by omega)
  have hrel : (x-1)*(b-r*d) = 2*(r-ratio x)*d := by
    dsimp only [splitConversionResidual, x, b, d] at hzero ⊢
    linarith
  have hx1 : x-1 ≠ 0 := by linarith
  have hd' : d ≠ 0 := hd
  have hb : b-r*d = 2*(r-ratio x)*d/(x-1) := by
    apply (eq_div_iff hx1).2
    linear_combination hrel
  calc
    b/d-r = (b-r*d)/d := by field_simp [hd']
    _ = (2*(r-ratio x)*d/(x-1))/d := by rw [hb]
    _ = 2*(r-ratio x)/(x-1) := by field_simp [hd',hx1]

theorem splitChartState_eq_finite_at_root (m : ℕ) (r δ : ℝ)
    (j : Fin (2*m+1))
    (hx : 1 < splitRoot δ j.val)
    (hd : (splitRawD m r δ).eval (ratio (splitRoot δ j.val)) ≠ 0)
    (hv : r-ratio (splitRoot δ j.val) ≠ 0) :
    splitChartState m r δ (splitRoot δ j.val) =
      splitFiniteState m r δ j := by
  let x := splitRoot δ j.val
  let d := (splitRawD m r δ).eval (ratio x)
  let b := (splitRawB m r δ).eval (ratio x)
  let ell := b/d-r
  have hell : ell = 2*(r-ratio x)/(x-1) :=
    splitChartEll_eq_at_root m r δ j hx hd
  have hvalues := chart_values_at_conversion_root x r d ell hx hd hv hell
  unfold splitChartState splitFiniteState
  dsimp only
  rw [hvalues.1, hvalues.2]

/-- The fixed-enzyme-total chart remains in the physical positive region
on a neighborhood of every prescribed root with positive conversion data. -/
theorem splitChartState_eventually_positive_at_root (m : ℕ)
    (r δ : ℝ) (j : Fin (2*m+1))
    (hD : DensePositive (splitRawD m r δ) m)
    (hB : DensePositive (splitRawB m r δ) m)
    (hx : 1 < splitRoot δ j.val)
    (hv : 0 < r-ratio (splitRoot δ j.val)) :
    ∀ᶠ y in 𝓝 (splitRoot δ j.val),
      (splitChartState m r δ y).Positive := by
  let x0 := splitRoot δ j.val
  let D := splitRawD m r δ
  let B := splitRawB m r δ
  have hd : D.eval (ratio x0) ≠ 0 :=
    ne_of_gt (hD.eval_pos (ratio_pos hx))
  have hell0 : 0 < B.eval (ratio x0)/D.eval (ratio x0)-r := by
    rw [splitChartEll_eq_at_root m r δ j hx hd]
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
    (hbc.div hdc hd).sub continuousAt_const
  have hvc : ContinuousAt (fun y : ℝ => r-ratio y) x0 :=
    continuousAt_const.sub hratio
  have hnearx : ∀ᶠ y in 𝓝 x0, 1 < y := Ioi_mem_nhds hx
  have hnearv : ∀ᶠ y in 𝓝 x0, 0 < r-ratio y :=
    hvc.eventually (Ioi_mem_nhds hv)
  have hnearell : ∀ᶠ y in 𝓝 x0,
      0 < B.eval (ratio y)/D.eval (ratio y)-r :=
    hec.eventually (Ioi_mem_nhds hell0)
  filter_upwards [hnearx, hnearv, hnearell] with y hyx hyv hyell
  exact splitChartState_positive m r δ y hyx hD hB hyv hyell

theorem splitChartResidual_at_root (m : ℕ) (r δ : ℝ)
    (j : Fin (2*m+1))
    (hD : DensePositive (splitRawD m r δ) m)
    (hx : 1 < splitRoot δ j.val)
    (hv : 0 < r-ratio (splitRoot δ j.val)) :
    splitChartResidual m r δ (splitRoot δ j.val) = 0 := by
  let x := splitRoot δ j.val
  let d := (splitRawD m r δ).eval (ratio x)
  let b := (splitRawB m r δ).eval (ratio x)
  have hd : d ≠ 0 := ne_of_gt (hD.eval_pos (ratio_pos hx))
  have hellpos : 0 < b/d-r := by
    rw [splitChartEll_eq_at_root m r δ j hx hd]
    exact div_pos (mul_pos (by norm_num) hv) (sub_pos.mpr hx)
  have hell : b/d-r ≠ 0 := ne_of_gt hellpos
  have hellv : b/d-ratio x ≠ 0 := by
    have : 0 < b/d-ratio x := by linarith
    exact ne_of_gt this
  rw [splitChartResidual_eq_multiplier_mul m r δ x hx hd hell hellv]
  rw [splitConversionResidual_at_root m j.val r δ (by omega)]
  ring

end
end PhosphorylationStableCapacity
