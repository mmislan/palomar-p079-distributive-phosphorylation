module
public import proofs.PhosphorylationStableCapacity.SplitChartResidual

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section

open PhosphorylationSharpness Polynomial

/-- The substrate-total residual's numerator after clearing the positive
chart denominators, expressed in the balance gap `e=b-rd`. -/
def chartClearedNumerator (x v e d : ℝ) : ℝ :=
  v*d*(e+v*d) - 2*ratio x*e^2

def chartConversionCore (x v e d : ℝ) : ℝ :=
  (x-1)*e - 2*v*d

def chartCompanion (x v e d : ℝ) : ℝ :=
  (x+1)*e + 2*v*d

/-- A denominator-free factorization, valid at every real argument. -/
theorem chartClearedNumerator_factor (x v e d : ℝ) :
    4*chartClearedNumerator x v e d =
      -chartConversionCore x v e d * chartCompanion x v e d := by
  unfold chartClearedNumerator chartConversionCore chartCompanion ratio
  ring

def splitChartClearedNumerator (m : ℕ) (r δ x : ℝ) : ℝ :=
  let u := ratio x
  let b := (splitRawB m r δ).eval u
  let d := (splitRawD m r δ).eval u
  chartClearedNumerator x (r-u) (b-r*d) d

def splitChartCompanion (m : ℕ) (r δ x : ℝ) : ℝ :=
  let u := ratio x
  let b := (splitRawB m r δ).eval u
  let d := (splitRawD m r δ).eval u
  chartCompanion x (r-u) (b-r*d) d

theorem splitChartClearedNumerator_factor (m : ℕ) (r δ x : ℝ) :
    4*splitChartClearedNumerator m r δ x =
      -splitConversionResidual m r δ x *
        splitChartCompanion m r δ x := by
  exact chartClearedNumerator_factor x (r-ratio x)
    ((splitRawB m r δ).eval (ratio x)-
      r*(splitRawD m r δ).eval (ratio x))
    ((splitRawD m r δ).eval (ratio x))

theorem splitConversionResidual_at_root (m j : ℕ) (r δ : ℝ)
    (hj : j < 2*m+1) :
    splitConversionResidual m r δ (splitRoot δ j) = 0 := by
  rw [show splitConversionResidual m r δ (splitRoot δ j) =
      (4*r*(splitPair m δ).1.eval r+
        (splitRoot δ j-1)*(splitPair m δ).2.eval r) *
        splitScalarProduct m δ (splitRoot δ j) from
    split_conversion_residual_factor m r δ (splitRoot δ j)]
  rw [splitScalarProduct_eq_prod_range]
  have hmem : j ∈ Finset.range (2*m+1) := Finset.mem_range.mpr hj
  rw [Finset.prod_eq_zero hmem (by simp)]
  ring

theorem splitChartCompanion_pos_at_root (m j : ℕ) (r δ : ℝ)
    (hj : j < 2*m+1)
    (hx : 1 < splitRoot δ j)
    (hv : 0 < r-ratio (splitRoot δ j))
    (hd : 0 < (splitRawD m r δ).eval (ratio (splitRoot δ j))) :
    0 < splitChartCompanion m r δ (splitRoot δ j) := by
  let x := splitRoot δ j
  let v := r-ratio x
  let d := (splitRawD m r δ).eval (ratio x)
  let e := (splitRawB m r δ).eval (ratio x)-r*d
  have hzero := splitConversionResidual_at_root m j r δ hj
  have hcore : (x-1)*e = 2*v*d := by
    dsimp [splitConversionResidual, x, v, d, e] at hzero ⊢
    linarith
  have hepos : 0 < e := by
    have hh : 0 < (x-1)*e := by
      rw [hcore]
      exact mul_pos (mul_pos (by norm_num) hv) hd
    exact (mul_pos_iff_of_pos_left (sub_pos.mpr hx)).mp hh
  have hfirst : 0 < (x+1)*e := mul_pos (by linarith) hepos
  have hsecond : 0 < 2*v*d := mul_pos (mul_pos (by norm_num) hv) hd
  change 0 < (x+1)*e+2*v*d
  linarith

theorem splitConversionResidual_differentiable (m : ℕ) (r δ : ℝ) :
    Differentiable ℝ (fun x => splitConversionResidual m r δ x) := by
  unfold splitConversionResidual ratio
  fun_prop

theorem splitChartCompanion_differentiable (m : ℕ) (r δ : ℝ) :
    Differentiable ℝ (fun x => splitChartCompanion m r δ x) := by
  unfold splitChartCompanion chartCompanion ratio
  dsimp
  fun_prop

/-- At each prescribed root, the cleared substrate numerator has the
opposite derivative sign from the converted balance residual. -/
theorem splitChartClearedNumerator_deriv_at_root (m j : ℕ)
    (r δ : ℝ) (hj : j < 2*m+1) :
    deriv (fun x => splitChartClearedNumerator m r δ x) (splitRoot δ j) =
      -(splitChartCompanion m r δ (splitRoot δ j)/4) *
        deriv (fun x => splitConversionResidual m r δ x)
          (splitRoot δ j) := by
  let f : ℝ → ℝ := fun x => splitConversionResidual m r δ x
  let g : ℝ → ℝ := fun x => splitChartCompanion m r δ x
  have heq : (fun x => splitChartClearedNumerator m r δ x) =
      fun x => -(1/4 : ℝ) * (f x * g x) := by
    funext x
    have h := splitChartClearedNumerator_factor m r δ x
    dsimp [f, g]
    linarith
  have hprod : (fun x => f x * g x) = f * g := rfl
  have hdf : DifferentiableAt ℝ f (splitRoot δ j) :=
    (splitConversionResidual_differentiable m r δ).differentiableAt
  have hdg : DifferentiableAt ℝ g (splitRoot δ j) :=
    (splitChartCompanion_differentiable m r δ).differentiableAt
  have hz : f (splitRoot δ j) = 0 :=
    splitConversionResidual_at_root m j r δ hj
  rw [heq, deriv_const_mul_field, hprod,
    deriv_mul hdf hdg]
  simp [f, g, hz]
  ring

theorem splitChartClearedNumerator_deriv_alternates (m j : ℕ)
    {r δ : ℝ} (hr : 0 < r) (hδ : 0 < δ)
    (hj : j < 2*m+1)
    (hv : 0 < r-ratio (splitRoot δ j))
    (hd : 0 < (splitRawD m r δ).eval (ratio (splitRoot δ j))) :
    (Even j → deriv (fun x => splitChartClearedNumerator m r δ x)
      (splitRoot δ j) < 0) ∧
    (Odd j → 0 < deriv (fun x => splitChartClearedNumerator m r δ x)
      (splitRoot δ j)) := by
  have hx : 1 < splitRoot δ j := by
    have hnonneg : 0 ≤ δ*(j:ℝ) := mul_nonneg hδ.le (Nat.cast_nonneg _)
    dsimp [splitRoot]
    linarith
  have hK := splitChartCompanion_pos_at_root m j r δ hj hx hv hd
  have hfactor : -(splitChartCompanion m r δ (splitRoot δ j)/4) < 0 :=
    neg_neg_of_pos (div_pos hK (by norm_num))
  have hR := splitConversionResidual_deriv_alternates m j hr hδ hj
  rw [splitChartClearedNumerator_deriv_at_root m j r δ hj]
  exact ⟨fun he => mul_neg_of_neg_of_pos hfactor (hR.1 he),
    fun ho => mul_pos_of_neg_of_neg hfactor (hR.2 ho)⟩

end
end PhosphorylationStableCapacity
