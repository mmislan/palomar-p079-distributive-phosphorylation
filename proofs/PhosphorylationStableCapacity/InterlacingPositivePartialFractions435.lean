module
public import Mathlib.LinearAlgebra.Lagrange
public import Mathlib.Basic.Real.Basic
public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

@[expose] public section
set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

namespace PhosphorylationStableCapacity
noncomputable section
open Polynomial
open scoped BigOperators

/-- Complete finite factorizations, with the paper's decreasing root order.
The magnitudes of the numerator roots exceed the matched denominator roots. -/
structure NegativeInterlacingFactorization (p q : ℝ[X]) (m : ℕ) where
  numeratorRoots : Fin m → ℝ
  denominatorRoots : Fin m → ℝ
  numerator_strictAnti : StrictAnti numeratorRoots
  denominator_strictAnti : StrictAnti denominatorRoots
  matched_lt : ∀ i, numeratorRoots i < denominatorRoots i
  cross_lt : ∀ i j, i < j → denominatorRoots j < numeratorRoots i
  denominator_neg : ∀ i, denominatorRoots i < 0
  numerator_leading_pos : 0 < p.leadingCoeff
  denominator_leading_pos : 0 < q.leadingCoeff
  numerator_factorization : p = C p.leadingCoeff * Lagrange.nodal Finset.univ numeratorRoots
  denominator_factorization : q = C q.leadingCoeff * Lagrange.nodal Finset.univ denominatorRoots

namespace NegativeInterlacingFactorization
variable {p q : ℝ[X]} {m : ℕ} (h : NegativeInterlacingFactorization p q m)

def numeratorResidue (i : Fin m) : ℝ :=
  p.eval (h.denominatorRoots i) *
    Lagrange.nodalWeight Finset.univ h.denominatorRoots i / q.leadingCoeff

def denominatorResidue (i : Fin m) : ℝ :=
  -(q.eval (h.numeratorRoots i) *
    Lagrange.nodalWeight Finset.univ h.numeratorRoots i / p.leadingCoeff)

private theorem denominator_difference_product_ne_zero (i : Fin m) :
    (∏ j ∈ (Finset.univ : Finset (Fin m)).erase i,
      (h.denominatorRoots i-h.denominatorRoots j)) ≠ 0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro j hj
  apply sub_ne_zero.mpr
  intro he
  exact (Finset.mem_erase.mp hj).1 (h.denominator_strictAnti.injective he).symm

private theorem numerator_difference_product_ne_zero (i : Fin m) :
    (∏ j ∈ (Finset.univ : Finset (Fin m)).erase i,
      (h.numeratorRoots i-h.numeratorRoots j)) ≠ 0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro j hj
  apply sub_ne_zero.mpr
  intro he
  exact (Finset.mem_erase.mp hj).1 (h.numerator_strictAnti.injective he).symm

theorem numeratorResidue_pos (i : Fin m) : 0 < h.numeratorResidue i := by
  classical
  have hquot : 0 < ∏ j ∈ (Finset.univ : Finset (Fin m)).erase i,
      (h.denominatorRoots i-h.numeratorRoots j) /
        (h.denominatorRoots i-h.denominatorRoots j) := by
    apply Finset.prod_pos
    intro j hj
    rcases lt_or_gt_of_ne (Finset.mem_erase.mp hj).1 with hji | hij
    · exact div_pos_of_neg_of_neg (sub_neg.mpr (h.cross_lt j i hji))
        (sub_neg.mpr (h.denominator_strictAnti hji))
    · exact div_pos
        (sub_pos.mpr (lt_trans (h.matched_lt j)
          (h.denominator_strictAnti hij)))
        (sub_pos.mpr (h.denominator_strictAnti hij))
  have hformula : h.numeratorResidue i =
      (p.leadingCoeff/q.leadingCoeff)*(h.denominatorRoots i-h.numeratorRoots i)*
        (∏ j ∈ (Finset.univ : Finset (Fin m)).erase i,
          (h.denominatorRoots i-h.numeratorRoots j)/
            (h.denominatorRoots i-h.denominatorRoots j)) := by
    unfold numeratorResidue
    have heval : p.eval (h.denominatorRoots i) = p.leadingCoeff *
        (Lagrange.nodal Finset.univ h.numeratorRoots).eval (h.denominatorRoots i) := by
      have he := congrArg (fun z : ℝ[X] => z.eval (h.denominatorRoots i))
        h.numerator_factorization
      simpa only [eval_mul, eval_C] using he
    rw [heval, Lagrange.eval_nodal,
      Lagrange.nodalWeight_eq_eval_nodal_erase_inv, Lagrange.eval_nodal]
    rw [← Finset.mul_prod_erase (Finset.univ : Finset (Fin m))
      (fun j => h.denominatorRoots i-h.numeratorRoots j) (Finset.mem_univ i)]
    rw [Finset.prod_div_distrib]
    ring
  rw [hformula]
  exact mul_pos (mul_pos (div_pos h.numerator_leading_pos h.denominator_leading_pos)
    (sub_pos.mpr (h.matched_lt i))) hquot

theorem denominatorResidue_pos (i : Fin m) : 0 < h.denominatorResidue i := by
  classical
  have hquot : 0 < ∏ j ∈ (Finset.univ : Finset (Fin m)).erase i,
      (h.numeratorRoots i-h.denominatorRoots j) /
        (h.numeratorRoots i-h.numeratorRoots j) := by
    apply Finset.prod_pos
    intro j hj
    rcases lt_or_gt_of_ne (Finset.mem_erase.mp hj).1 with hji | hij
    · exact div_pos_of_neg_of_neg
        (sub_neg.mpr (lt_trans (h.numerator_strictAnti hji) (h.matched_lt j)))
        (sub_neg.mpr (h.numerator_strictAnti hji))
    · exact div_pos (sub_pos.mpr (h.cross_lt i j hij))
        (sub_pos.mpr (h.numerator_strictAnti hij))
  have hformula : h.denominatorResidue i =
      (q.leadingCoeff/p.leadingCoeff)*(h.denominatorRoots i-h.numeratorRoots i)*
        (∏ j ∈ (Finset.univ : Finset (Fin m)).erase i,
          (h.numeratorRoots i-h.denominatorRoots j)/
            (h.numeratorRoots i-h.numeratorRoots j)) := by
    unfold denominatorResidue
    have heval : q.eval (h.numeratorRoots i) = q.leadingCoeff *
        (Lagrange.nodal Finset.univ h.denominatorRoots).eval (h.numeratorRoots i) := by
      have he := congrArg (fun z : ℝ[X] => z.eval (h.numeratorRoots i))
        h.denominator_factorization
      simpa only [eval_mul, eval_C] using he
    rw [heval, Lagrange.eval_nodal,
      Lagrange.nodalWeight_eq_eval_nodal_erase_inv, Lagrange.eval_nodal]
    rw [← Finset.mul_prod_erase (Finset.univ : Finset (Fin m))
      (fun j => h.numeratorRoots i-h.denominatorRoots j) (Finset.mem_univ i)]
    rw [Finset.prod_div_distrib]
    ring
  rw [hformula]
  exact mul_pos (mul_pos (div_pos h.denominator_leading_pos h.numerator_leading_pos)
    (sub_pos.mpr (h.matched_lt i))) hquot

theorem numeratorResidue_eq_derivative (i : Fin m) :
    h.numeratorResidue i = p.eval (h.denominatorRoots i) /
      q.derivative.eval (h.denominatorRoots i) := by
  unfold numeratorResidue
  have hderiv : q.derivative.eval (h.denominatorRoots i) = q.leadingCoeff *
      (Lagrange.nodal Finset.univ h.denominatorRoots).derivative.eval (h.denominatorRoots i) := by
    have he := congrArg (fun z : ℝ[X] => z.derivative.eval (h.denominatorRoots i))
      h.denominator_factorization
    simpa only [derivative_C_mul, eval_mul, eval_C] using he
  rw [hderiv,
    Lagrange.nodalWeight_eq_eval_derivative_nodal (Finset.mem_univ i)]
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

theorem denominatorResidue_eq_derivative (i : Fin m) :
    h.denominatorResidue i = -q.eval (h.numeratorRoots i) /
      p.derivative.eval (h.numeratorRoots i) := by
  unfold denominatorResidue
  have hderiv : p.derivative.eval (h.numeratorRoots i) = p.leadingCoeff *
      (Lagrange.nodal Finset.univ h.numeratorRoots).derivative.eval (h.numeratorRoots i) := by
    have he := congrArg (fun z : ℝ[X] => z.derivative.eval (h.numeratorRoots i))
      h.numerator_factorization
    simpa only [derivative_C_mul, eval_mul, eval_C] using he
  rw [hderiv,
    Lagrange.nodalWeight_eq_eval_derivative_nodal (Finset.mem_univ i)]
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

theorem denominator_root_derivative_ne_zero (i : Fin m) :
    q.derivative.eval (h.denominatorRoots i) ≠ 0 := by
  intro hz
  have hs := h.numeratorResidue_pos i
  rw [h.numeratorResidue_eq_derivative, hz, div_zero] at hs
  exact (lt_irrefl (0 : ℝ)) hs

theorem numerator_root_derivative_ne_zero (i : Fin m) :
    p.derivative.eval (h.numeratorRoots i) ≠ 0 := by
  intro hz
  have hs := h.denominatorResidue_pos i
  rw [h.denominatorResidue_eq_derivative, hz, div_zero] at hs
  exact (lt_irrefl (0 : ℝ)) hs

end NegativeInterlacingFactorization

/-- Equal-degree polynomial division into simple nodal partial fractions.
This is an algebraic Lagrange interpolation identity; it includes degree zero. -/
theorem nodal_partial_fraction_identity
    {m : ℕ} (p q : ℝ[X]) (v : Fin m → ℝ)
    (hinj : Function.Injective v) (hp : 0 < p.leadingCoeff) (hq : 0 < q.leadingCoeff)
    (hpdeg : p.degree = (m : WithBot ℕ))
    (hqfac : q = C q.leadingCoeff * Lagrange.nodal Finset.univ v)
    (u : ℝ) (hu : ∀ i, u ≠ v i) :
    p.eval u / q.eval u = p.leadingCoeff/q.leadingCoeff +
      ∑ i, (p.eval (v i)*Lagrange.nodalWeight Finset.univ v i/q.leadingCoeff)/(u-v i) := by
  classical
  let α := p.leadingCoeff/q.leadingCoeff
  let f := p-C α*q
  have hα : α ≠ 0 := div_ne_zero (ne_of_gt hp) (ne_of_gt hq)
  have hqdeg : q.degree = (m : WithBot ℕ) := by
    rw [hqfac, degree_C_mul (ne_of_gt hq), Lagrange.degree_nodal]
    simp
  have hdegree : f.degree < (m : WithBot ℕ) := by
    have hdegeq : p.degree = (C α*q).degree := by rw [degree_C_mul hα, hpdeg, hqdeg]
    have hlead : p.leadingCoeff = (C α*q).leadingCoeff := by
      rw [leadingCoeff_mul, leadingCoeff_C]
      exact (div_mul_cancel₀ _ (ne_of_gt hq)).symm
    exact hpdeg ▸ degree_sub_lt_left hdegeq
      (Polynomial.leadingCoeff_ne_zero.mp (ne_of_gt hp)) hlead
  have hnodes : ∀ i, q.eval (v i) = 0 := by
    intro i
    rw [hqfac, eval_mul, eval_C, Lagrange.eval_nodal_at_node (Finset.mem_univ i), mul_zero]
  have hinterp : f = Lagrange.interpolate Finset.univ v (fun i => p.eval (v i)) := by
    apply Lagrange.eq_interpolate_of_eval_eq _ hinj.injOn
    · simpa using hdegree
    · intro i _
      simp only [f, eval_sub, eval_mul, eval_C, hnodes i, mul_zero, sub_zero]
  have hnodal : (Lagrange.nodal Finset.univ v).eval u ≠ 0 :=
    Lagrange.eval_nodal_not_at_node (fun i _ => hu i)
  have hqu : q.eval u ≠ 0 := by
    rw [hqfac, eval_mul, eval_C]
    exact mul_ne_zero (ne_of_gt hq) hnodal
  have heval : p.eval u-α*q.eval u =
      (Lagrange.nodal Finset.univ v).eval u *
        ∑ i, Lagrange.nodalWeight Finset.univ v i*(u-v i)⁻¹*p.eval (v i) := by
    have he := congrArg (fun z : ℝ[X] => z.eval u) hinterp
    rw [Lagrange.eval_interpolate_not_at_node _ (fun i _ => hu i)] at he
    simpa only [f, eval_sub, eval_mul, eval_C] using he
  have hsum : (∑ i, (p.eval (v i)*Lagrange.nodalWeight Finset.univ v i/q.leadingCoeff)/(u-v i)) =
      (∑ i, Lagrange.nodalWeight Finset.univ v i*(u-v i)⁻¹*p.eval (v i))/q.leadingCoeff := by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro i _
    simp only [div_eq_mul_inv]
    ring
  rw [hsum]
  have hqeval : q.eval u = q.leadingCoeff*(Lagrange.nodal Finset.univ v).eval u := by
    conv_lhs => rw [hqfac]
    simp only [eval_mul, eval_C]
  change p.eval u/q.eval u = α+_
  apply (div_eq_iff hqu).mpr
  rw [add_mul]
  have hdiv :
      ((∑ i, Lagrange.nodalWeight Finset.univ v i*(u-v i)⁻¹*p.eval (v i))/q.leadingCoeff)*q.eval u =
        (Lagrange.nodal Finset.univ v).eval u *
          ∑ i, Lagrange.nodalWeight Finset.univ v i*(u-v i)⁻¹*p.eval (v i) := by
    rw [hqeval]
    field_simp [ne_of_gt hq]
  rw [hdiv]
  linarith [heval]

namespace NegativeInterlacingFactorization
variable {p q : ℝ[X]} {m : ℕ} (h : NegativeInterlacingFactorization p q m)

theorem numerator_partial_fractions (u : ℝ) (hu : ∀ i, u ≠ h.denominatorRoots i) :
    p.eval u/q.eval u = p.leadingCoeff/q.leadingCoeff +
      ∑ i, h.numeratorResidue i/(u-h.denominatorRoots i) := by
  apply nodal_partial_fraction_identity p q h.denominatorRoots
    h.denominator_strictAnti.injective h.numerator_leading_pos h.denominator_leading_pos
  · rw [h.numerator_factorization, degree_C_mul (ne_of_gt h.numerator_leading_pos),
      Lagrange.degree_nodal]
    simp
  · exact h.denominator_factorization
  · exact hu

theorem denominator_partial_fractions (u : ℝ) (hu : ∀ i, u ≠ h.numeratorRoots i) :
    q.eval u/p.eval u = q.leadingCoeff/p.leadingCoeff -
      ∑ i, h.denominatorResidue i/(u-h.numeratorRoots i) := by
  have he := nodal_partial_fraction_identity q p h.numeratorRoots
    h.numerator_strictAnti.injective h.denominator_leading_pos h.numerator_leading_pos
    (by rw [h.denominator_factorization, degree_C_mul (ne_of_gt h.denominator_leading_pos),
         Lagrange.degree_nodal]; simp) h.numerator_factorization u hu
  simpa only [denominatorResidue, neg_div, Finset.sum_neg_distrib, sub_neg_eq_add] using he

end NegativeInterlacingFactorization
end
end PhosphorylationStableCapacity
