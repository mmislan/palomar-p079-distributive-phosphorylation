module
public import Mathlib.Analysis.Polynomial.Basic
public import Mathlib.Algebra.Polynomial.Eval.Coeff
public import Mathlib.Topology.Algebra.Polynomial
public import Mathlib.Topology.Order.IntermediateValue
public import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Multiset
public import Mathlib.Algebra.BigOperators.Ring.Multiset
public import Mathlib.Algebra.Ring.Parity

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section

open Polynomial Filter
open scoped Topology

/-- A positive leading coefficient gives a positive value at a positive
argument, including for a constant polynomial. -/
theorem positiveLeadingCoeff_exists_positive_eval
    (p : ℝ[X]) (hleading : 0 < p.leadingCoeff) :
    ∃ t : ℝ, 0 < t ∧ 0 < p.eval t := by
  by_cases hdegree : p.natDegree = 0
  · have hcoeff : p.coeff 0 = p.leadingCoeff := by
      simpa only [hdegree] using (Polynomial.coeff_natDegree (p := p))
    refine ⟨1, zero_lt_one, ?_⟩
    rw [Polynomial.eq_C_of_natDegree_eq_zero hdegree, Polynomial.eval_C, hcoeff]
    exact hleading
  · have ht : Tendsto (fun t : ℝ => p.eval t) atTop atTop :=
      p.tendsto_atTop_of_leadingCoeff_nonneg
        (Polynomial.natDegree_pos_iff_degree_pos.mp (Nat.pos_of_ne_zero hdegree))
        hleading.le
    exact ((eventually_gt_atTop (0 : ℝ)).and (ht.eventually_gt_atTop 0)).exists

/-- A real polynomial with positive leading coefficient, no positive real
root and nonzero constant term has a positive constant term. Complex roots
are unrestricted. -/
theorem positiveLeadingCoeff_eval_zero_pos_of_no_positive_root
    (p : ℝ[X]) (hleading : 0 < p.leadingCoeff) (hzero : p.eval 0 ≠ 0)
    (hnoroot : ∀ x : ℝ, 0 < x → p.eval x ≠ 0) :
    0 < p.eval 0 := by
  by_contra hpositive
  have hnegative : p.eval 0 < 0 :=
    lt_of_le_of_ne (le_of_not_gt hpositive) hzero
  obtain ⟨t, ht, hvalue⟩ := positiveLeadingCoeff_exists_positive_eval p hleading
  obtain ⟨x, hx, hroot⟩ := intermediate_value_Icc ht.le p.continuous.continuousOn
    (show (0 : ℝ) ∈ Set.Icc (p.eval 0) (p.eval t) from ⟨hnegative.le, hvalue.le⟩)
  have hxne : x ≠ 0 := by
    intro heq
    subst x
    exact hzero hroot
  exact hnoroot x (lt_of_le_of_ne hx.1 hxne.symm) hroot

/-- The sign at zero forces odd positive-real-root multiplicity.

The filtered multiset contains every positive real root with its full
multiplicity. Its monic linear-factor product is removed from `p`; the
remaining factor has no positive real roots and a positive constant term
by the intermediate value theorem. No splitting over the reals is assumed. -/
theorem positive_real_root_multiplicity_odd_of_eval_zero_neg
    (p : ℝ[X]) (hleading : 0 < p.leadingCoeff) (hzero : p.eval 0 < 0) :
    Odd ((p.roots.filter (fun x : ℝ => 0 < x)).card) := by
  classical
  let s : Multiset ℝ := p.roots.filter (fun x : ℝ => 0 < x)
  let f : ℝ[X] := (s.map (fun x : ℝ => X - C x)).prod
  have hp : p ≠ 0 := Polynomial.leadingCoeff_ne_zero.mp hleading.ne'
  have hs : s ≤ p.roots := Multiset.filter_le _ _
  have hfdvd : f ∣ p := (Multiset.prod_X_sub_C_dvd_iff_le_roots hp s).mpr hs
  obtain ⟨q, hpq⟩ := hfdvd
  have hq : q ≠ 0 := by
    intro hqzero
    apply hp
    rw [hpq, hqzero, mul_zero]
  have hqleading : 0 < q.leadingCoeff := by
    have hleading_eq : p.leadingCoeff = q.leadingCoeff := by
      rw [hpq]
      exact Polynomial.leadingCoeff_monic_mul (Polynomial.monic_multisetProd_X_sub_C s)
    rwa [hleading_eq] at hleading
  have hqzero : q.eval 0 ≠ 0 := by
    intro hz
    apply hzero.ne
    rw [hpq, Polynomial.eval_mul, hz, mul_zero]
  have hroots : p.roots = s + q.roots := by
    rw [hpq, Polynomial.roots_mul (hpq ▸ hp)]
    change (s.map (fun x : ℝ => X - C x)).prod.roots + q.roots = s + q.roots
    rw [Polynomial.roots_multiset_prod_X_sub_C]
  have hspositive : ∀ x ∈ s, 0 < x := by
    intro x hx
    exact (Multiset.mem_filter.mp hx).2
  have hself : s.filter (fun x : ℝ => 0 < x) = s :=
    Multiset.filter_eq_self.mpr hspositive
  have hqfilter : q.roots.filter (fun x : ℝ => 0 < x) = 0 := by
    have hfiltered := congrArg (Multiset.filter (fun x : ℝ => 0 < x)) hroots
    change s = (s + q.roots).filter (fun x : ℝ => 0 < x) at hfiltered
    rw [Multiset.filter_add, hself] at hfiltered
    exact add_eq_left.mp hfiltered.symm
  have hqnoroot : ∀ x : ℝ, 0 < x → q.eval x ≠ 0 := by
    intro x hx hroot
    have hmem : x ∈ q.roots.filter (fun y : ℝ => 0 < y) :=
      Multiset.mem_filter.mpr ⟨(Polynomial.mem_roots hq).mpr hroot, hx⟩
    rw [hqfilter] at hmem
    simp at hmem
  have hqpositive : 0 < q.eval 0 :=
    positiveLeadingCoeff_eval_zero_pos_of_no_positive_root q hqleading hqzero hqnoroot
  have hsprod : 0 < s.prod := Multiset.prod_pos hspositive
  have hfzero : f.eval 0 = (-1 : ℝ) ^ s.card * s.prod := by
    dsimp only [f]
    simp only [Polynomial.eval_multiset_prod, Multiset.map_map, Function.comp_def,
      Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, zero_sub]
    exact Multiset.prod_map_neg s
  apply Nat.not_even_iff_odd.mp
  intro heven
  have hpzero_positive : 0 < p.eval 0 := by
    rw [hpq, Polynomial.eval_mul, hfzero, heven.neg_one_pow, one_mul]
    exact mul_pos hsprod hqpositive
  exact (not_lt_of_ge hpzero_positive.le) hzero

/-- Monic adapter for a real characteristic polynomial. -/
theorem monic_positive_real_root_multiplicity_odd_of_coeff_zero_neg
    (p : ℝ[X]) (hmonic : p.Monic) (hzero : p.coeff 0 < 0) :
    Odd ((p.roots.filter (fun x : ℝ => 0 < x)).card) := by
  apply positive_real_root_multiplicity_odd_of_eval_zero_neg p
  · rw [hmonic.leadingCoeff]
    exact zero_lt_one
  · rw [← Polynomial.coeff_zero_eq_eval_zero]
    exact hzero

end
end PhosphorylationStableCapacity
