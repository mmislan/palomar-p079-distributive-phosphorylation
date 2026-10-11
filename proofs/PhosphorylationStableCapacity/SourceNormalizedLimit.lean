module
public import Mathlib.Algebra.BigOperators.Field
public import proofs.PhosphorylationSharpness.Assembly
public import proofs.PhosphorylationStableCapacity.CoalescedCoefficientMoments

@[expose] public section

namespace PhosphorylationStableCapacity

open Polynomial Filter PhosphorylationSharpness
open scoped Topology BigOperators

noncomputable section

/-- The finite-parameter denominator for the coalesced complex concentrations
has the leading coefficient predicted by the inherited conversion. -/
theorem rawD_eval_one_scaled_limit {p q : ℝ[X]} {m : ℕ}
    (hp : DensePositive p m) (hq : DensePositive q m) :
    Tendsto (fun r : ℝ => (rawD p q r).eval 1 / r ^ m) atTop
      (𝓝 (4 * p.coeff m * q.eval 1)) := by
  have heval (r : ℝ) :
      (rawD p q r).eval 1 / r ^ m =
        ∑ i : Fin (m + 1), (rawD p q r).coeff i / r ^ m := by
    have hdeg : (rawD p q r).natDegree < m + 1 := by
      apply Nat.lt_succ_of_le
      apply natDegree_le_iff_coeff_eq_zero.mpr
      intro i hi
      exact (raw_support hp hq r i hi).1
    rw [eval_eq_sum_range' hdeg]
    simp only [one_pow, mul_one]
    rw [Finset.sum_div]
    exact (Fin.sum_univ_eq_sum_range
      (fun i => (rawD p q r).coeff i / r ^ m) (m + 1)).symm
  have hcoeff : Tendsto
      (fun r : ℝ => ∑ i : Fin (m + 1), (rawD p q r).coeff i / r ^ m)
      atTop (𝓝 (∑ i : Fin (m + 1), 4 * p.coeff m * q.coeff i)) := by
    apply tendsto_finsetSum (Finset.univ : Finset (Fin (m + 1)))
    intro i _
    exact rawD_scaled_limit hp hq i
  have hsum : (∑ i : Fin (m + 1), 4 * p.coeff m * q.coeff i) =
      4 * p.coeff m * q.eval 1 := by
    rw [← Finset.mul_sum]
    have hqsum : (∑ i : Fin (m + 1), q.coeff i) = q.eval 1 := by
      simpa [inventory] using dense_inventory hq 1
    rw [hqsum]
  simpa only [heval, hsum] using hcoeff

/-- Normalized finite-parameter phosphatase-complex coefficient. -/
def finiteD (p q : ℝ[X]) (r : ℝ) (i : ℕ) : ℝ :=
  (rawD p q r).coeff i / (rawD p q r).eval 1

/-- Normalized finite-parameter kinase-complex coefficient. -/
def finiteB (p q : ℝ[X]) (r : ℝ) (i : ℕ) : ℝ :=
  (rawB p q r).coeff i / (rawD p q r).eval 1

theorem finiteD_tendsto {p q : ℝ[X]} {m : ℕ}
    (hp : DensePositive p m) (hq : DensePositive q m) (i : ℕ) :
    Tendsto (fun r : ℝ => finiteD p q r i) atTop
      (𝓝 (q.coeff i / q.eval 1)) := by
  have hpm : 0 < p.coeff m := hp.1 m le_rfl
  have hq1 : 0 < q.eval 1 := hq.eval_pos (by norm_num)
  have hden := rawD_eval_one_scaled_limit hp hq
  have hlim := (rawD_scaled_limit hp hq i).div hden
    (ne_of_gt (mul_pos (mul_pos (by norm_num) hpm) hq1))
  have hcalc : (4 * p.coeff m * q.coeff i) /
      (4 * p.coeff m * q.eval 1) = q.coeff i / q.eval 1 := by
    field_simp [ne_of_gt hpm, ne_of_gt hq1]
  rw [hcalc] at hlim
  apply hlim.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with r hr
  simp only [finiteD]
  exact div_div_div_cancel_right₀ (ne_of_gt (pow_pos hr m)) _ _

theorem finiteB_scaled_tendsto {p q : ℝ[X]} {m : ℕ}
    (hp : DensePositive p m) (hq : DensePositive q m) (i : ℕ) :
    Tendsto (fun r : ℝ => finiteB p q r i / r) atTop
      (𝓝 ((p.coeff i + q.coeff i) / q.eval 1)) := by
  have hpm : 0 < p.coeff m := hp.1 m le_rfl
  have hq1 : 0 < q.eval 1 := hq.eval_pos (by norm_num)
  have hden := rawD_eval_one_scaled_limit hp hq
  have hlim := (rawB_scaled_limit hp hq i).div hden
    (ne_of_gt (mul_pos (mul_pos (by norm_num) hpm) hq1))
  have hcalc : (4 * p.coeff m * (q.coeff i + p.coeff i)) /
      (4 * p.coeff m * q.eval 1) =
      (p.coeff i + q.coeff i) / q.eval 1 := by
    field_simp [ne_of_gt hpm, ne_of_gt hq1]
    ring
  rw [hcalc] at hlim
  apply hlim.congr'
  have hdenpos : ∀ᶠ r : ℝ in atTop,
      0 < (rawD p q r).eval 1 / r ^ m :=
    hden.eventually (Ioi_mem_nhds
      (mul_pos (mul_pos (by norm_num) hpm) hq1))
  filter_upwards [eventually_gt_atTop (0 : ℝ), hdenpos] with r hr hdp
  have hD : (rawD p q r).eval 1 ≠ 0 := by
    exact ne_of_gt ((div_pos_iff_of_pos_right (pow_pos hr m)).mp hdp)
  simp only [finiteB]
  change ((rawB p q r).coeff i / r ^ (m + 1)) /
      ((rawD p q r).eval 1 / r ^ m) =
        ((rawB p q r).coeff i / (rawD p q r).eval 1) / r
  rw [pow_succ]
  field_simp [ne_of_gt hr, ne_of_gt (pow_pos hr m), hD]

end
end PhosphorylationStableCapacity
