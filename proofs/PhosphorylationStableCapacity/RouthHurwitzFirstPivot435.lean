module
public import proofs.PhosphorylationStableCapacity.LocalRouthAlternation435
public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Multiset

@[expose] public section
set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

namespace PhosphorylationStableCapacity

open Polynomial Matrix

noncomputable section

private theorem routh_complex_re_multiset_sum (s : Multiset ℂ) :
    s.sum.re = (s.map Complex.re).sum := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons z s ih => simp [Complex.add_re, ih]

/-- A positive-leading nonconstant real Hurwitz polynomial has a
strictly positive next coefficient. The proof uses all roots with their
multiplicities and their strictly negative real parts; no numerical
root approximations or Routh certificate is assumed. -/
theorem hurwitzPolynomial_nextCoeff_pos
    (p : ℝ[X]) (hdegree : 0 < p.natDegree)
    (hleading : 0 < p.leadingCoeff)
    (hstable : ∀ z : ℂ,
      (p.map (algebraMap ℝ ℂ)).eval z = 0 → z.re < 0) :
    0 < p.nextCoeff := by
  classical
  let P : ℂ[X] := p.map (algebraMap ℝ ℂ)
  have hsplit : P.Splits := IsAlgClosed.splits P
  have hdeg : 0 < P.natDegree := by
    simpa [P, Polynomial.natDegree_map] using hdegree
  have hnonempty : P.roots ≠ 0 := hsplit.roots_ne_zero (ne_of_gt hdeg)
  have hroots (z : ℂ) (hz : z ∈ P.roots) : z.re < 0 :=
    hstable z (Polynomial.isRoot_of_mem_roots hz)
  have hsum : (P.roots.map Complex.re).sum < 0 := by
    have hstrict : (P.roots.map Complex.re).sum <
        (P.roots.map (fun _ => (0 : ℝ))).sum :=
      Multiset.sum_lt_sum_of_nonempty
        (f := Complex.re) (g := fun _ => (0 : ℝ)) hnonempty hroots
    simpa using hstrict
  have hnext : P.nextCoeff = (p.nextCoeff : ℂ) := by
    simpa [P] using Polynomial.nextCoeff_map_eq p (algebraMap ℝ ℂ)
  have hlead : P.leadingCoeff = (p.leadingCoeff : ℂ) := by
    simp [P]
  have hidentity : p.nextCoeff =
      -p.leadingCoeff*(P.roots.map Complex.re).sum := by
    have h := congrArg Complex.re hsplit.nextCoeff_eq_neg_sum_roots_mul_leadingCoeff
    rw [hnext, hlead] at h
    simpa [Complex.mul_re, Complex.neg_re, routh_complex_re_multiset_sum] using h
  rw [hidentity]
  exact mul_pos_of_neg_of_neg (neg_lt_zero.mpr hleading) hsum

/-- The generic stable-polynomial root-sum theorem supplies precisely
the first pivot required by the explicit determinant reduction. -/
theorem routhHurwitz_first_pivot_pos
    (p : ℝ[X]) (hdegree : 0 < p.natDegree)
    (hleading : 0 < p.leadingCoeff)
    (hstable : ∀ z : ℂ,
      (p.map (algebraMap ℝ ℂ)).eval z = 0 → z.re < 0) :
    0 < routhDescendingCoeff p.natDegree p 1 := by
  have hnext := hurwitzPolynomial_nextCoeff_pos p hdegree hleading hstable
  have hbound : (0 : ℤ) ≤ 1 ∧ (1 : ℤ) ≤ (p.natDegree : ℤ) := by omega
  unfold routhDescendingCoeff
  rw [ite_eq_left hbound]
  change 0 < p.coeff (p.natDegree-1)
  simpa only [← Polynomial.nextCoeff_of_natDegree_pos hdegree] using hnext

/-- The first proper Hurwitz-minor necessity is now unconditional on
Routh arrays for every nonconstant positive-leading Hurwitz polynomial. -/
theorem routhHurwitz_first_minor_pos
    (p : ℝ[X]) (hdegree : 0 < p.natDegree)
    (hleading : 0 < p.leadingCoeff)
    (hstable : ∀ z : ℂ,
      (p.map (algebraMap ℝ ℂ)).eval z = 0 → z.re < 0) :
    0 < routhHurwitzMinor p.natDegree 1 p := by
  simpa [routhHurwitzMinor, Matrix.det_fin_one, routhHurwitzMatrix] using
    routhHurwitz_first_pivot_pos p hdegree hleading hstable

end
end PhosphorylationStableCapacity
