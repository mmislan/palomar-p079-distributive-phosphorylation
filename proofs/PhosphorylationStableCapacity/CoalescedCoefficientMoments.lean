module
public import proofs.PhosphorylationStableCapacity.CoefficientMoments

@[expose] public section

namespace PhosphorylationStableCapacity

open PhosphorylationSharpness Polynomial

noncomputable section

/-- Positivity and exact support for the literal repeated-root source. -/
theorem coalescedPair_dense (m : ℕ) :
    DensePositive (coalescedPair m).1 m ∧
      DensePositive (coalescedPair m).2 m := by
  rw [coalescedPair_eq_source]
  have hps : ∀ ab ∈ List.replicate m ((3 : ℝ), (3 : ℝ)),
      1 < ab.1 ∧ 1 < ab.2 := by
    intro ab hab
    simp only [List.mem_replicate] at hab
    rcases hab with ⟨_, rfl⟩
    norm_num
  simpa using prescribedPair_dense 3 (List.replicate m (3, 3))
    (by norm_num) hps

theorem coalescedPair_coeff_sums (m : ℕ) :
    (∑ i ∈ Finset.range (m + 1), (coalescedPair m).1.coeff i) = (36 : ℝ)^m ∧
      (∑ i ∈ Finset.range (m + 1), (coalescedPair m).2.coeff i) =
        (36 : ℝ)^m := by
  have hdense := coalescedPair_dense m
  have hdegN : (coalescedPair m).1.natDegree ≤ m :=
    Polynomial.natDegree_le_iff_coeff_eq_zero.mpr hdense.1.2
  have hdegJ : (coalescedPair m).2.natDegree ≤ m :=
    Polynomial.natDegree_le_iff_coeff_eq_zero.mpr hdense.2.2
  constructor
  · rw [← eval_one_eq_coeff_sum _ m hdegN]
    exact (coalescedPair_eval_one m).1
  · rw [← eval_one_eq_coeff_sum _ m hdegJ]
    exact (coalescedPair_eval_one m).2

theorem coalescedPair_coeff_first_moments (m : ℕ) :
    (∑ i ∈ Finset.range (m + 2),
      (coalescedPair (m + 1)).1.coeff i * (i : ℝ)) =
        (36 : ℝ)^(m + 1) * ((4 * (m : ℝ) + 2) / 9) ∧
    (∑ i ∈ Finset.range (m + 2),
      (coalescedPair (m + 1)).2.coeff i * (i : ℝ)) =
        (36 : ℝ)^(m + 1) * ((4 * (m : ℝ) + 8) / 9) := by
  have hdense := coalescedPair_dense (m + 1)
  have hdegN : (coalescedPair (m + 1)).1.natDegree ≤ m + 1 :=
    Polynomial.natDegree_le_iff_coeff_eq_zero.mpr hdense.1.2
  have hdegJ : (coalescedPair (m + 1)).2.natDegree ≤ m + 1 :=
    Polynomial.natDegree_le_iff_coeff_eq_zero.mpr hdense.2.2
  constructor
  · rw [← derivative_eval_one_eq_coeff_moment _ (m + 1) hdegN]
    exact (coalescedPair_deriv_eval_one m).1
  · rw [← derivative_eval_one_eq_coeff_moment _ (m + 1) hdegJ]
    exact (coalescedPair_deriv_eval_one m).2

end
end PhosphorylationStableCapacity
