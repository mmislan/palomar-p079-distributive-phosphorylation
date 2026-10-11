module
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section
open Matrix
open scoped BigOperators

/-- A symmetric matrix's maximum absolute row sum bounds its quadratic form.
This is the exact norm estimate used in the finite recovery certificate. -/
theorem symmetric_quadratic_le_of_rowBound {ι : Type*} [Fintype ι]
    (P : Matrix ι ι ℝ) (hP : P.IsSymm) (M : ℝ)
    (hrow : ∀ i, ∑ j, |P i j| ≤ M) (x : ι → ℝ) :
    x ⬝ᵥ (P *ᵥ x) ≤ M * (∑ i, x i ^ 2) := by
  have hentry (i j : ι) :
      2 * (P i j * x i * x j) ≤ |P i j| * (x i ^ 2 + x j ^ 2) := by
    have habs : P i j * x i * x j ≤ |P i j| * |x i| * |x j| := by
      simpa only [abs_mul] using le_abs_self (P i j * x i * x j)
    have hs : 2 * (|x i| * |x j|) ≤ x i ^ 2 + x j ^ 2 := by
      nlinarith [sq_nonneg (|x i| - |x j|), sq_abs (x i), sq_abs (x j)]
    have hm := mul_le_mul_of_nonneg_left hs (abs_nonneg (P i j))
    nlinarith
  have hcols (j : ι) : ∑ i, |P i j| ≤ M := by
    simpa only [hP.apply] using hrow j
  have hquad : x ⬝ᵥ (P *ᵥ x) = ∑ i, ∑ j, P i j * x i * x j := by
    simp only [Matrix.mulVec, dotProduct, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hs : 2 * (x ⬝ᵥ (P *ᵥ x)) ≤
      ∑ i, ∑ j, |P i j| * (x i ^ 2 + x j ^ 2) := by
    rw [hquad, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum (fun j _ => hentry i j)
  have hsplit : (∑ i, ∑ j, |P i j| * (x i ^ 2 + x j ^ 2)) =
      (∑ i, (∑ j, |P i j|) * x i ^ 2) +
      (∑ j, (∑ i, |P i j|) * x j ^ 2) := by
    simp only [mul_add, Finset.sum_add_distrib]
    congr 1
    · simp only [Finset.sum_mul]
    · rw [Finset.sum_comm]
      simp only [Finset.sum_mul]
  have hleft : (∑ i, (∑ j, |P i j|) * x i ^ 2) ≤ M * (∑ i, x i ^ 2) := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_right (hrow i) (sq_nonneg _))
  have hright : (∑ j, (∑ i, |P i j|) * x j ^ 2) ≤ M * (∑ i, x i ^ 2) := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_right (hcols j) (sq_nonneg _))
  rw [hsplit] at hs
  linarith

/-- An exact right inverse and its absolute row bound give the reciprocal
coercivity bound for a positive definite matrix. No floating eigenvalue
estimate or unverified inverse computation is needed. -/
theorem posDef_quadratic_lower_of_inverse_rowBound {ι : Type*}
    [Fintype ι] [DecidableEq ι]
    (P R : Matrix ι ι ℝ) (hP : P.PosDef) (hR : R.IsSymm)
    (hPR : P * R = 1) (M : ℝ) (hM : 0 < M)
    (hrow : ∀ i, ∑ j, |R i j| ≤ M) (x : ι → ℝ) :
    (∑ i, x i ^ 2) / M ≤ x ⬝ᵥ (P *ᵥ x) := by
  have hPx : P *ᵥ (R *ᵥ x) = x := by
    rw [Matrix.mulVec_mulVec, hPR, Matrix.one_mulVec]
  have hcs := hP.star_dotProduct_mulVec_mul_le x (R *ᵥ x)
  simp only [star_trivial, hPx, dotProduct_comm (R *ᵥ x) x] at hcs
  have hxx : x ⬝ᵥ x = ∑ i, x i ^ 2 := by
    simp only [dotProduct, pow_two]
  rw [hxx] at hcs
  have hupper := symmetric_quadratic_le_of_rowBound R hR M hrow x
  have hPnonneg : 0 ≤ x ⬝ᵥ (P *ᵥ x) := by
    simpa only [star_trivial] using hP.posSemidef.dotProduct_mulVec_nonneg x
  have hmul := mul_le_mul_of_nonneg_left hupper hPnonneg
  have hsum : 0 ≤ ∑ i, x i ^ 2 := Finset.sum_nonneg (fun i _ => sq_nonneg _)
  rw [div_le_iff₀ hM]
  by_cases hz : (∑ i, x i ^ 2) = 0
  · rw [hz]
    exact mul_nonneg hPnonneg hM.le
  · have hpos : 0 < ∑ i, x i ^ 2 := lt_of_le_of_ne hsum (Ne.symm hz)
    nlinarith

end
end PhosphorylationStableCapacity
