module
public import proofs.PhosphorylationStableCapacity.ArbitrarySplitReadout435
public import proofs.PhosphorylationStableCapacity.CoefficientMoments

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section

open PhosphorylationSharpness Polynomial

/-- The scalar readout function for a fixed conversion polynomial. -/
def splitReadoutScalar (m : ℕ) (D : ℝ[X]) (x : ℝ) : ℝ :=
  (D.coeff m / 2) * ((ratio x)^m / D.eval (ratio x)) *
    ((x-1)*(x+5)/(x+1))

theorem splitReadoutScalar_hasDerivAt_three (m : ℕ) (D : ℝ[X])
    (hD : D.eval 1 ≠ 0) :
    HasDerivAt (splitReadoutScalar m D)
      ((D.coeff m / 2) *
        (3 * ((m : ℝ)*D.eval 1-D.derivative.eval 1)/(D.eval 1)^2 +
          3/(2*D.eval 1))) 3 := by
  have hu : HasDerivAt ratio (3/4) 3 := by
    convert (((hasDerivAt_id (3 : ℝ)).pow 2).sub_const 1).div_const 8 using 1
    · funext x; rfl
    · norm_num
  have hnum : HasDerivAt (fun x => (ratio x)^m) ((m : ℝ)*3/4) 3 := by
    convert hu.pow m using 1
    · norm_num [ratio]; ring
  have hratio3 : ratio 3 = 1 := by norm_num [ratio]
  have hden : HasDerivAt (fun x => D.eval (ratio x))
      (D.derivative.eval 1 * (3/4)) 3 := by
    have houter : HasDerivAt (fun y => D.eval y) (D.derivative.eval 1) (ratio 3) := by
      simpa only [hratio3] using D.hasDerivAt 1
    convert houter.comp 3 hu using 1
    funext x; rfl
  have hg : HasDerivAt (fun x : ℝ => (x-1)*(x+5)/(x+1)) (3/2) 3 := by
    convert (((hasDerivAt_id (3 : ℝ)).sub_const 1).mul
      ((hasDerivAt_id (3 : ℝ)).add_const 5)).div
      ((hasDerivAt_id (3 : ℝ)).add_const 1) (by norm_num) using 1
    · funext x; rfl
    · norm_num
  have h := ((hnum.div hden (by simpa only [hratio3] using hD)).const_mul
      (D.coeff m / 2)).mul hg
  convert h using 1
  · ext x; rfl
  · simp only [hratio3, one_pow, Pi.div_apply] at *
    field_simp [hD]
    ring

theorem densePolynomial_moment_deficit_nonneg (m : ℕ) (D : ℝ[X])
    (hD : DensePositive D m) :
    0 ≤ (m : ℝ)*D.eval 1-D.derivative.eval 1 := by
  have hdeg : D.natDegree ≤ m := hD.degree_eq.le
  rw [eval_one_eq_coeff_sum D m hdeg,
    derivative_eval_one_eq_coeff_moment D m hdeg]
  have hsum : 0 ≤ ∑ i ∈ Finset.range (m+1),
      D.coeff i * ((m : ℝ) - (i : ℝ)) := by
    apply Finset.sum_nonneg
    intro i hi
    have him : i ≤ m := by have := Finset.mem_range.mp hi; omega
    have hcoeff : 0 ≤ D.coeff i := le_of_lt (hD.1 i him)
    have hcast : (i : ℝ) ≤ (m : ℝ) := by exact_mod_cast him
    exact mul_nonneg hcoeff (sub_nonneg.mpr hcast)
  convert hsum using 1
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  ring

/-- The coalesced readout has a strictly positive first derivative. -/
theorem splitReadoutScalar_deriv_three_pos (m : ℕ) (D : ℝ[X])
    (hD : DensePositive D m) :
    0 < deriv (splitReadoutScalar m D) 3 := by
  have hval : 0 < D.eval 1 := hD.eval_pos (by norm_num)
  rw [(splitReadoutScalar_hasDerivAt_three m D (ne_of_gt hval)).deriv]
  have hmoment := densePolynomial_moment_deficit_nonneg m D hD
  have hleading : 0 < D.coeff m := hD.1 m le_rfl
  have hfirst : 0 ≤ 3 * ((m : ℝ)*D.eval 1-D.derivative.eval 1) /
      (D.eval 1)^2 := div_nonneg (mul_nonneg (by norm_num) hmoment) (sq_nonneg _)
  have hsecond : 0 < 3 / (2*D.eval 1) := by positivity
  exact mul_pos (by linarith) (add_pos_of_nonneg_of_pos hfirst hsecond)

end

end PhosphorylationStableCapacity
