module
public import proofs.PhosphorylationStableCapacity.SourceJacobianAugmentedOrientation

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section
open PhosphorylationSharpness

/-- The corrected scalar orientation pivot has a direct physical
formula: free substrate plus the free-phosphatase share of all bound
complexes. This identity holds at every positive literal state. -/
theorem source_moment_pivot_formula {n : ℕ}
    (x : State n) (hx : x.Positive) :
    sourcePathZerothMoment (sourceAugmentedTotalRow x) -
      sourcePathZerothMoment (sourceOccupancyDifference x) *
        (∑ i : Fin n, x.C i) =
      (∑ j : Fin (n+1), x.S j) +
        x.F / totalF x *
          ((∑ i : Fin n, x.C i) + (∑ i : Fin n, x.D i)) := by
  let C := ∑ i : Fin n, x.C i
  let D := ∑ i : Fin n, x.D i
  let S := ∑ j : Fin (n+1), x.S j
  have hET : totalE x = x.E + C := by rfl
  have hFT : totalF x = x.F + D := by rfl
  have hETpos : 0 < totalE x := by
    rw [hET]
    exact add_pos_of_pos_of_nonneg hx.2.1
      (Finset.sum_nonneg fun i _ => (hx.2.2.2.1 i).le)
  have hFTpos : 0 < totalF x := by
    rw [hFT]
    exact add_pos_of_pos_of_nonneg hx.2.2.1
      (Finset.sum_nonneg fun i _ => (hx.2.2.2.2 i).le)
  have hrow (j : Fin (n+1)) :
      sourceAugmentedTotalRow x j = x.S j +
        sourceLevelC x j * x.E / totalE x +
        sourceLevelD x j * x.F / totalF x := by
    have h := loadedBindingMass_column_sum_general
      x.S (sourceLevelC x) (sourceLevelD x)
      (totalE x) (totalF x) x.E x.F
      (by simp [totalE, sourceLevelC_sum])
      (by simp [totalF, sourceLevelD_sum])
      (ne_of_gt hETpos) (ne_of_gt hFTpos) j
    simpa [sourceAugmentedTotalRow, totalAndLevelOutputMatrix,
      Matrix.mul_apply] using h
  have hT0 : sourcePathZerothMoment (sourceAugmentedTotalRow x) =
      S + C*x.E/totalE x + D*x.F/totalF x := by
    simp only [sourcePathZerothMoment]
    simp_rw [hrow]
    simp only [Finset.sum_add_distrib, ← Finset.sum_div,
      ← Finset.sum_mul, sourceLevelC_sum, sourceLevelD_sum]
    rfl
  have hQ0 : sourcePathZerothMoment (sourceOccupancyDifference x) =
      D/totalF x - C/totalE x := by
    simp [sourcePathZerothMoment, sourceOccupancyDifference,
      Finset.sum_sub_distrib, ← Finset.sum_div,
      sourceLevelC_sum, sourceLevelD_sum, C, D]
  rw [hT0, hQ0]
  change S + C*x.E/(x.E+C) + D*x.F/(x.F+D) -
    (D/(x.F+D)-C/(x.E+C))*C = S + x.F/(x.F+D)*(C+D)
  have hE0 : x.E+C ≠ 0 := by rw [← hET]; exact ne_of_gt hETpos
  have hF0 : x.F+D ≠ 0 := by rw [← hFT]; exact ne_of_gt hFTpos
  field_simp [hE0, hF0]
  ring

theorem source_moment_pivot_pos {n : ℕ}
    (x : State n) (hx : x.Positive) :
    0 < sourcePathZerothMoment (sourceAugmentedTotalRow x) -
      sourcePathZerothMoment (sourceOccupancyDifference x) *
        (∑ i : Fin n, x.C i) := by
  rw [source_moment_pivot_formula x hx]
  have hS : 0 < ∑ j : Fin (n+1), x.S j :=
    Finset.sum_pos (fun j _ => hx.1 j) Finset.univ_nonempty
  have hF : 0 < x.F / totalF x := by
    apply div_pos hx.2.2.1
    dsimp [totalF]
    exact add_pos_of_pos_of_nonneg hx.2.2.1
      (Finset.sum_nonneg fun i _ => (hx.2.2.2.2 i).le)
  have hC : 0 ≤ ∑ i : Fin n, x.C i :=
    Finset.sum_nonneg fun i _ => (hx.2.2.2.1 i).le
  have hD : 0 ≤ ∑ i : Fin n, x.D i :=
    Finset.sum_nonneg fun i _ => (hx.2.2.2.2 i).le
  exact add_pos_of_pos_of_nonneg hS
    (mul_nonneg hF.le (add_nonneg hC hD))

end
end PhosphorylationStableCapacity
