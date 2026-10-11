module
public import proofs.PhosphorylationStableCapacity.CoalescedPathLimitTransfer

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section

open Polynomial PhosphorylationSharpness

/-- Exact leading coefficients of the repeated-root numerator and
phosphatase-complex polynomials. -/
theorem coalescedPair_leading_coefficients (m : ℕ) :
    (coalescedPair m).1.coeff m = (8 : ℝ)^m ∧
      (coalescedPair m).2.coeff m = (3 * (m : ℝ) + 1) * (8 : ℝ)^m := by
  induction m with
  | zero => simp [coalescedPair]
  | succ m ih =>
      have hd := coalescedPair_dense m
      have hpzero : (coalescedPair m).1.coeff (m+1) = 0 :=
        hd.1.2 (m+1) (by omega)
      have hqzero : (coalescedPair m).2.coeff (m+1) = 0 :=
        hd.2.2 (m+1) (by omega)
      constructor
      · change (nextN 3 3 (coalescedPair m).1
          (coalescedPair m).2).coeff (m+1) = _
        simp only [nextN, coeff_add, coeff_C_mul, coeff_X_mul]
        rw [hpzero, hqzero, ih.1, pow_succ]
        ring
      · change (nextJ 3 3 (coalescedPair m).1
          (coalescedPair m).2).coeff (m+1) = _
        simp only [nextJ, coeff_add, coeff_C_mul, coeff_X_mul]
        rw [hqzero, ih.1, ih.2, pow_succ]
        push_cast
        ring

/-- The manuscript's exact normalized leading coefficient
`v_n = (3n-2)(2/9)^(n-1)`, with `n=m+2`. -/
theorem coalescedV_closed_form (m : ℕ) :
    coalescedV m = (3 * (m : ℝ) + 4) * (2 / 9 : ℝ)^(m+1) := by
  calc
    coalescedV m =
        (3 * (m : ℝ) + 4) * ((8 : ℝ) / 36)^(m+1) := by
      rw [coalescedV, coalescedYNext,
        (coalescedPair_leading_coefficients (m+1)).2, div_pow]
      push_cast
      ring
    _ = (3 * (m : ℝ) + 4) * (2 / 9 : ℝ)^(m+1) := by norm_num

/-- The actual finite path-feedback gain used in the coalesced prefix
stability certificate. -/
def coalescedFeedbackGain (m : ℕ) : ℝ :=
  ∑ i,
    coalescedPathEdgeFeedback m i *
      pathVectorFin (coalescedPathWeights m) i

/-- Closed stability deficit of the manuscript's limiting prefix block. -/
theorem coalescedFeedbackDeficit_closed_form (m : ℕ) :
    1 - coalescedFeedbackGain m =
      ((3 * (m : ℝ) + 4) * (50 * (m : ℝ) + 55) *
        (2 / 9 : ℝ)^(m+1)) /
      (9 * (14 - 8 * (3 * (m : ℝ) + 4) *
        (2 / 9 : ℝ)^(m+1))) := by
  have hv := coalescedV_bounds m
  have hden : 14 - 8 * coalescedV m ≠ 0 := by linarith
  have hgain := coalescedPath_feedback_gain m
  have hid := feedback_gain_identity ((m : ℝ) + 2)
    (coalescedV m) hden
  unfold coalescedFeedbackGain
  unfold coalescedPathEdgeFeedback
  rw [hgain]
  unfold coalescedMu
  have hrewrite :
      (10 * (4 / 3 - coalescedV m *
        ((m : ℝ) + 2 - (4 * (m : ℝ) + 5) / 9)) +
          (2 + coalescedV m) / 3) /
        (14 - 8 * coalescedV m) =
      (10 * ((4 : ℝ) / 3 - coalescedV m *
        (((m : ℝ) + 2) - (4 * ((m : ℝ) + 2) - 3) / 9)) +
          (2 + coalescedV m) / 3) /
        (14 - 8 * coalescedV m) := by ring
  rw [hrewrite, hid, coalescedV_closed_form]
  ring

/-- The source path block remains Hurwitz for every independent positive
choice of the prefix catalytic-current weights. -/
theorem coalescedPathBlock_hurwitz_any_positive_currents (m : ℕ)
    (ω : Fin (m+1) → ℝ) (hω : ∀ i, 0 < ω i) :
    IsHurwitz (coalescedPathBlock m * Matrix.diagonal ω) := by
  let w := pathVectorFin (coalescedPathWeights m)
  let v : Fin (m+1) → ℝ := fun i => w i / ω i
  have hw : ∀ i, 0 < w i :=
    pathVectorFin_pos (coalescedPathWeights m)
      (coalescedPathWeights_pos m)
  have hv : ∀ i, 0 < v i := fun i => div_pos (hw i) (hω i)
  apply hurwitz_of_metzler_positive_vector
    (coalescedPathBlock m * Matrix.diagonal ω) v hv
  · intro i j hij
    rw [Matrix.mul_diagonal]
    exact le_of_lt (mul_pos
      (coalescedPath_block_offdiag_pos m i j hij) (hω j))
  · intro i
    have hneg := coalescedPathBlock_negative_vector m i
    have heq :
        (∑ j, (coalescedPathBlock m * Matrix.diagonal ω) i j * v j) =
          ∑ j, coalescedPathBlock m i j * w j := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [Matrix.mul_diagonal]
      dsimp [v]
      field_simp [ne_of_gt (hω j)]
    rw [heq]
    exact hneg

end

end PhosphorylationStableCapacity
