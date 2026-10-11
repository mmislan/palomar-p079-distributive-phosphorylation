module
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section

/-- Adding a nonnegative-real-part number to a positive real multiple
of an open-right-half-plane number produces a nonzero number whose
reciprocal still has strictly positive real part. This is the scalar
positivity step in the Routh parity-ratio recursion. -/
theorem complex_positive_affine_inverse_real_part
    (c : ℝ) (z b : ℂ) (hc : 0 < c) (hz : 0 < z.re) (hb : 0 ≤ b.re) :
    (c : ℂ)*z+b ≠ 0 ∧ 0 < (((c : ℂ)*z+b)⁻¹).re := by
  have hre : 0 < ((c : ℂ)*z+b).re := by
    simpa only [Complex.add_re, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, sub_zero] using
      add_pos_of_pos_of_nonneg (mul_pos hc hz) hb
  have hne : (c : ℂ)*z+b ≠ 0 := by
    intro heq
    rw [heq, Complex.zero_re] at hre
    exact (lt_irrefl (0 : ℝ)) hre
  refine ⟨hne, ?_⟩
  rw [Complex.inv_re]
  exact div_pos hre (Complex.normSq_pos.mpr hne)

/-- The explicit ratio recursion transfers positivity to the reciprocal
ratio and forces its numerator to be nonzero. No root-count or Hurwitz
criterion is an assumption. -/
theorem routh_parity_ratio_inverse_positive
    (E O z : ℂ) (c : ℝ) (hc : 0 < c) (hz : 0 < z.re) (hO : O ≠ 0)
    (hb : 0 ≤ ((E-(c : ℂ)*z*O)/O).re) :
    E ≠ 0 ∧ 0 < (O/E).re := by
  let b : ℂ := (E-(c : ℂ)*z*O)/O
  have heq : E/O = (c : ℂ)*z+b := by
    dsimp only [b]
    field_simp [hO]
    ring
  obtain ⟨ha, hinv⟩ := complex_positive_affine_inverse_real_part c z b hc hz hb
  have hE : E ≠ 0 := by
    intro hzero
    apply ha
    rw [← heq, hzero, zero_div]
  refine ⟨hE, ?_⟩
  have hpositive : 0 < ((E/O)⁻¹).re := by
    rw [heq]
    exact hinv
  simpa only [inv_div] using hpositive

/-- A sum cannot vanish when one summand is nonzero and the ratio of
the other to it has nonnegative real part. This discharges the final
nonvanishing implication in the open-right-half-plane parity argument. -/
theorem complex_sum_ne_zero_of_ratio_re_nonneg
    (E O : ℂ) (hE : E ≠ 0) (hratio : 0 ≤ (O/E).re) : E+O ≠ 0 := by
  intro hsum
  have hO : O = -E := by linear_combination hsum
  have hratioeq : O/E = -1 := by rw [hO]; simp [hE]
  rw [hratioeq] at hratio
  norm_num at hratio

end

end PhosphorylationStableCapacity
