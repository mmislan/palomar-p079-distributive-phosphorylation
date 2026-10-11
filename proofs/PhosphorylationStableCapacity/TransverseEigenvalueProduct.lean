module
public import proofs.PhosphorylationStableCapacity.HurwitzPolynomialConstantPositive
public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.Algebra.Polynomial.Splits

@[expose] public section

namespace PhosphorylationStableCapacity
noncomputable section
open Polynomial

/-- The actual product of the transverse roots, with algebraic multiplicity,
after deflating the simple zero eigenvalue of a real characteristic polynomial. -/
def transversePolynomialRootProduct (p : ℝ[X]) : ℂ :=
  ((p.divX.map (algebraMap ℝ ℂ)).roots).prod

/-- This is the manuscript's absolute transverse eigenvalue product, rather
than an independently chosen normalization constant. -/
theorem simple_neutral_transverse_root_product_norm
    (p : ℝ[X]) (q : ℂ[X]) (hp : p.Monic) (hp0 : p.coeff 0 = 0)
    (hfactor : p.map (algebraMap ℝ ℂ) = X*q)
    (hleft : ∀ z : ℂ, q.eval z = 0 → z.re < 0) :
    ‖transversePolynomialRootProduct p‖ = p.coeff 1 := by
  have hrealFactor : X*p.divX = p := by
    simpa only [hp0, Polynomial.C_0, add_zero] using Polynomial.X_mul_divX_add p
  have hmonic : p.divX.Monic :=
    Polynomial.monic_X.of_mul_monic_left (hrealFactor.symm ▸ hp)
  have hc : 0 < p.coeff 1 :=
    monic_simple_neutral_polynomial_coeff_one_pos p q hp hp0 hfactor hleft
  have hsplits := IsAlgClosed.splits (p.divX.map (algebraMap ℝ ℂ))
  have hprod := hsplits.coeff_zero_eq_prod_roots_of_monic
    (hmonic.map (algebraMap ℝ ℂ))
  have hnorm := congrArg (fun z : ℂ => ‖z‖) hprod
  simp only [norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul] at hnorm
  simpa only [transversePolynomialRootProduct, Polynomial.coeff_map,
    Polynomial.coeff_divX, zero_add, Complex.coe_algebraMap,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos hc] using hnorm.symm

/-- Removing the simple zero from the full root multiset leaves precisely
the roots whose product defines the transverse factor. -/
theorem zero_root_deflation_multiset
    (p : ℝ[X]) (hp : p.Monic) (hp0 : p.coeff 0 = 0) :
    (p.map (algebraMap ℝ ℂ)).roots.erase 0 =
      (p.divX.map (algebraMap ℝ ℂ)).roots := by
  have hrealFactor : X*p.divX = p := by
    simpa only [hp0, Polynomial.C_0, add_zero] using Polynomial.X_mul_divX_add p
  have hmap : p.map (algebraMap ℝ ℂ) =
      X*p.divX.map (algebraMap ℝ ℂ) := by
    conv_lhs => rw [← hrealFactor]
    rw [Polynomial.map_mul, Polynomial.map_X]
  have hnonzero : p.map (algebraMap ℝ ℂ) ≠ 0 :=
    (hp.map (algebraMap ℝ ℂ)).ne_zero
  have hroots : (p.map (algebraMap ℝ ℂ)).roots =
      (0 : ℂ) ::ₘ (p.divX.map (algebraMap ℝ ℂ)).roots := by
    rw [hmap, Polynomial.roots_mul (hmap ▸ hnonzero), Polynomial.roots_X,
      Multiset.singleton_add]
  rw [hroots, Multiset.erase_cons_head]

end
end PhosphorylationStableCapacity
