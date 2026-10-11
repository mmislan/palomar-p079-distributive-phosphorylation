module
public import proofs.PhosphorylationStableCapacity.SymmetricMatrixRowQuadraticBounds

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section
open Matrix
open scoped BigOperators

theorem symmetric_quadratic_le_of_variable_rowBound {ι : Type*} [Fintype ι]
    (P : Matrix ι ι ℝ) (hP : P.IsSymm) (M : ι → ℝ)
    (hrow : ∀ i, ∑ j, |P i j| ≤ M i) (x : ι → ℝ) :
    x ⬝ᵥ (P *ᵥ x) ≤ ∑ i, M i * x i ^ 2 := by
  have hentry (i j : ι) :
      2 * (P i j * x i * x j) ≤ |P i j| * (x i ^ 2 + x j ^ 2) := by
    have habs : P i j * x i * x j ≤ |P i j| * |x i| * |x j| := by
      simpa only [abs_mul] using le_abs_self (P i j * x i * x j)
    have hs : 2 * (|x i| * |x j|) ≤ x i ^ 2 + x j ^ 2 := by
      nlinarith [sq_nonneg (|x i| - |x j|), sq_abs (x i), sq_abs (x j)]
    have hm := mul_le_mul_of_nonneg_left hs (abs_nonneg (P i j))
    nlinarith
  have hcols (j : ι) : ∑ i, |P i j| ≤ M j := by
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
  have hleft : (∑ i, (∑ j, |P i j|) * x i ^ 2) ≤ ∑ i, M i * x i ^ 2 := by
    exact Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_right (hrow i) (sq_nonneg _))
  have hright : (∑ j, (∑ i, |P i j|) * x j ^ 2) ≤ ∑ j, M j * x j ^ 2 := by
    exact Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_right (hcols j) (sq_nonneg _))
  rw [hsplit] at hs
  linarith

/-- A positive uniform strict diagonal margin makes a real symmetric
matrix positive definite. This is a sound certificate interface for the
finite operational Q matrices. -/
theorem posDef_of_symmetric_strict_row_margin
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (Q : Matrix ι ι ℝ) (hQ : Q.IsSymm) (c : ℝ) (hc : 0 < c)
    (hmargin : ∀ i, ∑ j, |(diagonal (fun a => Q a a) - Q) i j| ≤ Q i i - c) :
    Q.PosDef := by
  have hR : (diagonal (fun a => Q a a) - Q).IsSymm := by
    rw [Matrix.IsSymm]
    ext i j
    simp only [Matrix.transpose_apply, Matrix.sub_apply]
    rw [hQ.apply i j]
    by_cases hij : i = j
    · subst j
      rfl
    · simp [hij, Ne.symm hij]
  have hHerm : Q.IsHermitian := by
    apply Matrix.IsHermitian.ext
    intro i j
    simpa only [star_trivial] using hQ.apply i j
  apply Matrix.PosDef.of_dotProduct_mulVec_pos hHerm
  intro x hx
  have hbound := symmetric_quadratic_le_of_variable_rowBound
    (diagonal (fun a => Q a a) - Q) hR (fun i => Q i i - c) hmargin x
  have hdiag : x ⬝ᵥ (diagonal (fun a => Q a a) *ᵥ x) =
      ∑ i, Q i i * x i ^ 2 := by
    simp only [dotProduct, Matrix.mulVec_diagonal]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [Matrix.sub_mulVec, dotProduct_sub, hdiag] at hbound
  have hsplit : (∑ i, (Q i i - c) * x i ^ 2) =
      (∑ i, Q i i * x i ^ 2) - c * (∑ i, x i ^ 2) := by
    simp [sub_mul, Finset.sum_sub_distrib, Finset.mul_sum]
  rw [hsplit] at hbound
  have hex : ∃ i, x i ≠ 0 := by
    by_contra hn
    push Not at hn
    exact hx (funext hn)
  obtain ⟨i, hi⟩ := hex
  have hsum : 0 < ∑ j, x j ^ 2 :=
    Finset.sum_pos' (fun j _ => sq_nonneg (x j))
      ⟨i, Finset.mem_univ i, sq_pos_of_ne_zero hi⟩
  have hpos := mul_pos hc hsum
  simpa only [star_trivial] using (show 0 < x ⬝ᵥ (Q *ᵥ x) by linarith)


end
end PhosphorylationStableCapacity
