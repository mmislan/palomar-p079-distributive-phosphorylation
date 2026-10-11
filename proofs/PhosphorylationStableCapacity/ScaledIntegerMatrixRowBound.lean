module
public import proofs.PhosphorylationStableCapacity.ScaledIntegerMatrixCertificates
public import Mathlib.Algebra.Order.BigOperators.Group.Finset

@[expose] public section

namespace PhosphorylationStableCapacity
noncomputable section
open Matrix
open scoped BigOperators

/-- Kernel-checked integer row inequalities bound a decoded rational
matrix's real row norm, including exact inverse norm certificates. -/
theorem ScaledIntegerMatrix.absolute_row_bound
    {ι κ : Type*} [Fintype κ]
    (A : ScaledIntegerMatrix ι κ) (hden : 0 < A.denominator)
    (num : ℤ) (den : ℕ) (hboundDen : 0 < den)
    (hrows : ∀ i, (∑ j, |A.entries i j|) * (den : ℤ) ≤
      num * (A.denominator : ℤ)) (i : ι) :
    (∑ j, |A.realMatrix i j|) ≤ (num : ℝ)/(den : ℝ) := by
  have ha : 0 < (A.denominator : ℝ) := Nat.cast_pos.mpr hden
  have hb : 0 < (den : ℝ) := Nat.cast_pos.mpr hboundDen
  have hr : (∑ j, |(A.entries i j : ℝ)|)*(den : ℝ) ≤
      (num : ℝ)*(A.denominator : ℝ) := by exact_mod_cast hrows i
  change (∑ j, |(A.denominator : ℝ)⁻¹ * (A.entries i j : ℝ)|) ≤ _
  simp_rw [abs_mul, abs_of_pos (inv_pos.mpr ha)]
  rw [← Finset.mul_sum]
  apply (le_div_iff₀ hb).mpr
  calc
    _ = (A.denominator : ℝ)⁻¹ * ((∑ j, |(A.entries i j : ℝ)|)*(den : ℝ)) := by ring
    _ ≤ (A.denominator : ℝ)⁻¹ * ((num : ℝ)*(A.denominator : ℝ)) :=
      mul_le_mul_of_nonneg_left hr (inv_nonneg.mpr ha.le)
    _ = (num : ℝ) := by field_simp

end
end PhosphorylationStableCapacity
