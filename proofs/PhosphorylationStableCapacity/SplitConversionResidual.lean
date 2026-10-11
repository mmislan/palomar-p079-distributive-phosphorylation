module
public import proofs.PhosphorylationStableCapacity.SplitScalarIdentity

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section

open PhosphorylationSharpness Polynomial

/-- The converted enzyme-balance residual is the source scalar residual
times an explicit source factor at every real argument, not only at its
prescribed zeros. -/
theorem conversion_residual_factor (p q : ℝ[X]) (r x : ℝ) :
    (x-1)*((rawB p q r).eval (ratio x)-r*(rawD p q r).eval (ratio x)) -
      2*(r-ratio x)*(rawD p q r).eval (ratio x) =
    (4*r*p.eval r+(x-1)*q.eval r)*
      ((x-1)*p.eval (ratio x)-2*q.eval (ratio x)) := by
  have h := congrArg (fun z : ℝ[X] => z.eval (ratio x))
    (quotient_identity p q r)
  simp only [eval_mul, eval_sub, eval_X, eval_C, conversionNumerator] at h
  simp only [rawB, rawD, eval_add, eval_sub, eval_mul, eval_C]
  dsimp [ratio] at h ⊢
  linear_combination 8*h

/-- For the literal split family the converted balance residual has exactly
the prescribed root product, with its explicit conversion prefactor. -/
theorem split_conversion_residual_factor (m : ℕ) (r δ x : ℝ) :
    (x-1)*((splitRawB m r δ).eval (ratio x)-
      r*(splitRawD m r δ).eval (ratio x)) -
      2*(r-ratio x)*(splitRawD m r δ).eval (ratio x) =
    (4*r*(splitPair m δ).1.eval r+
      (x-1)*(splitPair m δ).2.eval r)*
        splitScalarProduct m δ x := by
  rw [splitRawB, splitRawD, conversion_residual_factor,
    splitPair_scalar_identity]

def splitConversionResidual (m : ℕ) (r δ x : ℝ) : ℝ :=
  (x-1)*((splitRawB m r δ).eval (ratio x)-
      r*(splitRawD m r δ).eval (ratio x)) -
    2*(r-ratio x)*(splitRawD m r δ).eval (ratio x)

theorem conversion_prefactor_pos {p q : ℝ[X]} {m : ℕ}
    (hp : DensePositive p m) (hq : DensePositive q m)
    {r x : ℝ} (hr : 0 < r) (hx : 1 < x) :
    0 < 4*r*p.eval r+(x-1)*q.eval r := by
  have hpr := hp.eval_pos hr
  have hqr := hq.eval_pos hr
  have hfirst : 0 < 4*r*p.eval r :=
    mul_pos (mul_pos (by norm_num) hr) hpr
  have hsecond : 0 < (x-1)*q.eval r :=
    mul_pos (sub_pos.mpr hx) hqr
  linarith

/-- At a prescribed root, the derivative of the converted residual is the
strictly positive conversion factor times the source root-product derivative. -/
theorem splitConversionResidual_deriv_at_root (m j : ℕ) (r δ : ℝ)
    (hj : j < 2*m+1) :
    deriv (fun x => splitConversionResidual m r δ x) (splitRoot δ j) =
      (4*r*(splitPair m δ).1.eval r+
        (splitRoot δ j-1)*(splitPair m δ).2.eval r) *
          deriv (fun x => splitScalarProduct m δ x) (splitRoot δ j) := by
  let f : ℝ → ℝ := fun x =>
    4*r*(splitPair m δ).1.eval r+(x-1)*(splitPair m δ).2.eval r
  let g : ℝ → ℝ := fun x => splitScalarProduct m δ x
  have heq : (fun x => splitConversionResidual m r δ x) = f * g := by
    funext x
    exact split_conversion_residual_factor m r δ x
  have hz : g (splitRoot δ j) = 0 := by
    dsimp [g]
    rw [splitScalarProduct_eq_prod_range]
    apply Finset.prod_eq_zero (Finset.mem_range.mpr hj)
    simp
  have hdf : DifferentiableAt ℝ f (splitRoot δ j) := by
    dsimp [f]
    fun_prop
  have hdg : DifferentiableAt ℝ g (splitRoot δ j) := by
    have hprod : g =
        fun x => ∏ i ∈ Finset.range (2*m+1), (x - splitRoot δ i) := by
      funext x
      exact splitScalarProduct_eq_prod_range m δ x
    rw [hprod]
    fun_prop
  rw [heq, deriv_mul hdf hdg, hz]
  simp [f, g]

theorem splitConversionResidual_deriv_alternates (m j : ℕ)
    {r δ : ℝ} (hr : 0 < r) (hδ : 0 < δ) (hj : j < 2*m+1) :
    (Even j → 0 < deriv (fun x => splitConversionResidual m r δ x)
      (splitRoot δ j)) ∧
    (Odd j → deriv (fun x => splitConversionResidual m r δ x)
      (splitRoot δ j) < 0) := by
  obtain ⟨hp, hq⟩ := splitPair_dense m hδ.le
  have hx : 1 < splitRoot δ j := by
    have hnonneg : 0 ≤ δ*(j:ℝ) := mul_nonneg hδ.le (Nat.cast_nonneg _)
    dsimp [splitRoot]
    linarith
  have hfac := conversion_prefactor_pos hp hq hr hx
  have hs := splitScalarProduct_deriv_alternates m hδ j hj
  rw [splitConversionResidual_deriv_at_root m j r δ hj]
  exact ⟨fun he => mul_pos hfac (hs.1 he),
    fun ho => mul_neg_of_pos_of_neg hfac (hs.2 ho)⟩

end
end PhosphorylationStableCapacity
