module
public import proofs.PhosphorylationStableCapacity.HurwitzPolynomialConstantPositive
public import Mathlib.Analysis.RCLike.Lemmas
public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.Algebra.Polynomial.FieldDivision
public import Mathlib.Tactic.Linarith

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section
open Polynomial

/-- One possible simple nonnegative spectral point, together with positive
orientation, actually implies there is no right-half-plane point. This is the
generic even-index complement to the fixed-case small-gain certificates. -/
theorem monic_hurwitz_of_unique_simple_right_and_positive_constant
    (p : ℝ[X]) (hp : p.Monic) (hp0 : 0 < p.coeff 0)
    (hunique : ∀ z z' : ℂ,
      0 ≤ z.re → 0 ≤ z'.re →
      (p.map (algebraMap ℝ ℂ)).eval z = 0 →
      (p.map (algebraMap ℝ ℂ)).eval z' = 0 → z = z')
    (hsimple : ∀ z : ℂ, 0 ≤ z.re →
      (p.map (algebraMap ℝ ℂ)).eval z = 0 →
      ((p.map (algebraMap ℝ ℂ)).derivative).eval z ≠ 0) :
    ∀ z : ℂ, (p.map (algebraMap ℝ ℂ)).eval z = 0 → z.re < 0 := by
  intro z hz
  by_contra hleft
  have hznonneg : 0 ≤ z.re := le_of_not_gt hleft
  have hzAE : aeval z p = 0 := by
    simpa only [Polynomial.aeval_def, Polynomial.eval_map] using hz
  have hcAE : aeval (star z) p = 0 := by
    change aeval ((starRingEnd ℂ) z) p = 0
    rw [Polynomial.aeval_conj, hzAE, map_zero]
  have hconj : (p.map (algebraMap ℝ ℂ)).eval (star z) = 0 := by
    simpa only [Polynomial.aeval_def, Polynomial.eval_map] using hcAE
  have hfixed : star z = z :=
    (hunique z (star z) hznonneg (by simpa using hznonneg) hz hconj).symm
  have him : z.im = 0 := Complex.conj_eq_iff_im.mp hfixed
  let x : ℝ := z.re
  have hzreal : z = (x : ℂ) := by
    apply Complex.ext <;> simp [x, him]
  have hxnonneg : 0 ≤ x := hznonneg
  have hxroot : p.IsRoot x := by
    have hxAE : aeval (x : ℂ) p = 0 := by simpa only [← hzreal] using hzAE
    change p.eval x = 0
    change aeval (RCLike.ofReal x : ℂ) p = 0 at hxAE
    rw [Polynomial.aeval_ofReal] at hxAE
    exact RCLike.ofReal_eq_zero.mp hxAE
  have hxne : x ≠ 0 := by
    intro hzero
    have : p.coeff 0 = 0 := by
      change p.eval x = 0 at hxroot
      simpa only [hzero, Polynomial.coeff_zero_eq_eval_zero] using hxroot
    exact (ne_of_gt hp0) this
  have hxpos : 0 < x := lt_of_le_of_ne hxnonneg (Ne.symm hxne)
  let q : ℝ[X] := p /ₘ (X - C x)
  have hfactor : (X - C x) * q = p :=
    (Polynomial.mul_divByMonic_eq_iff_isRoot).mpr hxroot
  have hqmonic : q.Monic :=
    (Polynomial.monic_X_sub_C x).of_mul_monic_left (hfactor.symm ▸ hp)
  have hfactorC : (p.map (algebraMap ℝ ℂ)) =
      (X - C (x : ℂ)) * q.map (algebraMap ℝ ℂ) := by
    rw [← hfactor, Polynomial.map_mul, Polynomial.map_sub,
      Polynomial.map_X, Polynomial.map_C]
    rfl
  have hqleft : ∀ w : ℂ, (q.map (algebraMap ℝ ℂ)).eval w = 0 → w.re < 0 := by
    intro w hw
    by_contra hlt
    have hwnonneg : 0 ≤ w.re := le_of_not_gt hlt
    have hpw : (p.map (algebraMap ℝ ℂ)).eval w = 0 := by
      rw [hfactorC, Polynomial.eval_mul, hw, mul_zero]
    have hweq : w = (x : ℂ) :=
      (hunique w z hwnonneg hznonneg hpw hz).trans hzreal
    have hqx : (q.map (algebraMap ℝ ℂ)).eval (x : ℂ) = 0 := by
      rwa [hweq] at hw
    have hderiv : ((p.map (algebraMap ℝ ℂ)).derivative).eval (x : ℂ) =
        (q.map (algebraMap ℝ ℂ)).eval (x : ℂ) := by
      rw [hfactorC, Polynomial.derivative_mul, Polynomial.eval_add]
      simp
    apply hsimple z hznonneg hz
    rw [hzreal, hderiv]
    exact hqx
  have hq0 : 0 < q.coeff 0 :=
    monic_hurwitz_polynomial_constant_pos q hqmonic hqleft
  have hzero := congrArg (fun r : ℝ[X] => r.eval 0) hfactor
  simp only [Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_X,
    Polynomial.eval_C, zero_sub] at hzero
  have hqeval : 0 < q.eval 0 := by
    simpa only [Polynomial.coeff_zero_eq_eval_zero] using hq0
  have hpeval : 0 < p.eval 0 := by
    simpa only [Polynomial.coeff_zero_eq_eval_zero] using hp0
  nlinarith [mul_pos hxpos hqeval]

end
end PhosphorylationStableCapacity
