module
public import Mathlib.Analysis.Polynomial.Order
public import Mathlib.Algebra.Polynomial.Eval.Algebra
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Tactic.NormNum

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section
open Polynomial

/-- A real monic polynomial whose complex roots are strictly left has
positive constant coefficient. This identifies the absolute product of
the transverse eigenvalues in the manuscript splitting coefficient. -/
theorem monic_hurwitz_polynomial_constant_pos
    (p : ℝ[X]) (hp : p.Monic)
    (hleft : ∀ z : ℂ, (p.map (algebraMap ℝ ℂ)).eval z = 0 → z.re < 0) :
    0 < p.coeff 0 := by
  have hroots : ∀ y : ℝ, p.IsRoot y → y < 0 := by
    intro y hy
    have hmap := Polynomial.IsRoot.map (f := algebraMap ℝ ℂ) hy
    simpa only [Complex.ofReal_re] using hleft (y : ℂ) hmap.eq_zero
  have hpos := Polynomial.zero_lt_eval_of_roots_lt_of_leadingCoeff_nonneg
    hroots (show 0 ≤ p.leadingCoeff by rw [hp.leadingCoeff]; norm_num)
  simpa only [Polynomial.coeff_zero_eq_eval_zero] using hpos

/-- The linear characteristic coefficient is the positive constant
coefficient of the real deflated Hurwitz polynomial. -/
theorem monic_simple_neutral_polynomial_coeff_one_pos
    (p : ℝ[X]) (q : ℂ[X]) (hp : p.Monic) (hp0 : p.coeff 0 = 0)
    (hfactor : p.map (algebraMap ℝ ℂ) = X * q)
    (hleft : ∀ z : ℂ, q.eval z = 0 → z.re < 0) : 0 < p.coeff 1 := by
  have hrealFactor : X * p.divX = p := by
    simpa only [hp0, Polynomial.C_0, add_zero] using Polynomial.X_mul_divX_add p
  have hmonic : p.divX.Monic :=
    Polynomial.monic_X.of_mul_monic_left (hrealFactor.symm ▸ hp)
  have hmap : p.map (algebraMap ℝ ℂ) = X * p.divX.map (algebraMap ℝ ℂ) := by
    conv_lhs => rw [← hrealFactor]
    rw [Polynomial.map_mul, Polynomial.map_X]
  have hq : p.divX.map (algebraMap ℝ ℂ) = q := by
    apply mul_left_cancel₀ Polynomial.X_ne_zero
    exact hmap.symm.trans hfactor
  have hconst := monic_hurwitz_polynomial_constant_pos p.divX hmonic
    (fun z hz => hleft z (by rwa [← hq]))
  simpa only [Polynomial.coeff_divX, zero_add] using hconst

end
end PhosphorylationStableCapacity
