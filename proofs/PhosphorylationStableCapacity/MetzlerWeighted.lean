module
public import proofs.PhosphorylationStableCapacity.MetzlerHurwitz

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section

/-- A positive strict supersolution certifies Hurwitz stability for a Metzler matrix. -/
theorem hurwitz_of_metzler_positive_vector {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (w : ι → ℝ)
    (hw : ∀ i, 0 < w i)
    (hoff : ∀ i j, i ≠ j → 0 ≤ A i j)
    (hcert : ∀ i, (∑ j, A i j * w j) < 0) : IsHurwitz A := by
  let C : Matrix ι ι ℝ := fun i j => (w i)⁻¹ * A i j * w j
  have hC : C = Matrix.diagonal (fun i => (w i)⁻¹) * A * Matrix.diagonal w := by
    ext i j
    simp [C, mul_assoc]
  have hDE : Matrix.diagonal w * Matrix.diagonal (fun i => (w i)⁻¹) = 1 := by
    ext i j
    by_cases hij : i = j
    · subst j
      simp [ne_of_gt (hw i)]
    · simp [hij]
  have hchar : C.charpoly = A.charpoly := by
    rw [hC, Matrix.charpoly_mul_comm
      (Matrix.diagonal (fun i => (w i)⁻¹) * A) (Matrix.diagonal w)]
    rw [← mul_assoc, hDE, one_mul]
  have hoffC : ∀ i j, i ≠ j → 0 ≤ C i j := by
    intro i j hij
    exact mul_nonneg (mul_nonneg (le_of_lt (inv_pos.mpr (hw i)))
      (hoff i j hij)) (le_of_lt (hw j))
  have hrowC : ∀ i, (∑ j, C i j) < 0 := by
    intro i
    have hsum : (∑ j, C i j) = (w i)⁻¹ * (∑ j, A i j * w j) := by
      simp [C, Finset.mul_sum, mul_assoc]
    rw [hsum]
    exact mul_neg_of_pos_of_neg (inv_pos.mpr (hw i)) (hcert i)
  have hHurwitzC : IsHurwitz C :=
    hurwitz_of_metzler_strict_rows C hoffC hrowC
  intro z hz
  apply hHurwitzC z
  have hmap : (C.map (algebraMap ℝ ℂ)).charpoly =
      (A.map (algebraMap ℝ ℂ)).charpoly := by
    rw [Matrix.charpoly_map, Matrix.charpoly_map, hchar]
  rw [hmap]
  exact hz

end
end PhosphorylationStableCapacity
