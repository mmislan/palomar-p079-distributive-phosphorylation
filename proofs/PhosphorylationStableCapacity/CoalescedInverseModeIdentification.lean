module
public import proofs.PhosphorylationStableCapacity.CoalescedInverseForcingMoments
public import proofs.PhosphorylationStableCapacity.CoalescedInverseModeElimination

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section

/-- The literal limiting replacement equation yields the manuscript's
coordinate formula (5), scalar mode equations (6), and feedback (7). -/
theorem coalescedReplacementSolution_mode_identification (m : ℕ)
    (q x : Fin (m + 3) → ℝ)
    (hqsum : (∑ j : Fin (m + 3), q j) = 0)
    (hqlast : q (Fin.last (m + 2)) = 0)
    (hsol : (coalescedReplacementLimit m).mulVec x =
      coalescedReplacementTarget m q) :
    ∃ a b : ℝ,
      x = coalescedInverseParticular m q +
        coalescedFullKernelVector m a b ∧
      (3 * coalescedInverseT m q / 2 + coalescedInverseU m q) +
        (7 - 3 * coalescedV m) * a / 2 +
          3 * coalescedV m * b / 2 = 0 ∧
      (4 - coalescedV m) * b =
        coalescedInverseT m q + (1 - coalescedV m) * a ∧
      2 * b - a =
        (10 * coalescedInverseT m q +
          (2 + coalescedV m) * coalescedInverseU m q) /
            (2 * (7 - 4 * coalescedV m)) := by
  let a : ℝ :=
    (∑ j : Fin (m + 2), coalescedLevelWeight m j.val *
      (x j.castSucc - coalescedInverseParticular m q j.castSucc)) / 2
  let b : ℝ := x (Fin.last (m + 2))
  have hrepr : x = coalescedInverseParticular m q +
      coalescedFullKernelVector m a b := by
    funext j
    by_cases hj : j.val < m + 2
    · have heq : j = (⟨j.val, hj⟩ : Fin (m + 2)).castSucc := by
        ext
        rfl
      rw [heq]
      have hcoord := coalescedReplacementSolution_occupied_formula
        m q x hqsum hqlast hsol ⟨j.val, hj⟩
      simp only [Pi.add_apply]
      rw [coalescedInverseParticular_occupied]
      simpa [coalescedFullKernelVector, a, hj] using hcoord
    · have heq : j = Fin.last (m + 2) := by
        ext
        simp [Fin.val_last]
        omega
      rw [heq]
      simp [Pi.add_apply, coalescedInverseParticular_last,
        coalescedFullKernelVector, b, Fin.val_last]
  have hmode :
      (3 * coalescedInverseT m q / 2 + coalescedInverseU m q) +
        (7 - 3 * coalescedV m) * a / 2 +
          3 * coalescedV m * b / 2 = 0 := by
    have h := congrFun hsol (coalescedModeRow m)
    rw [hrepr, Matrix.mulVec_add, Pi.add_apply,
      coalescedInverseParticular_mode_action m q hqsum hqlast,
      coalescedReplacementLimit_mode_action] at h
    have hzero : 3 * coalescedInverseT m q / 2 + coalescedInverseU m q +
        ((7 - 3 * coalescedV m) * a / 2 +
          3 * coalescedV m * b / 2) = 0 := by
      simpa [coalescedReplacementTarget, coalescedModeRow] using h
    simpa only [add_assoc] using hzero
  have hfinal :
      -coalescedV m * coalescedInverseT m q / 2 +
        coalescedV m / 2 *
          ((4 - coalescedV m) * b - (1 - coalescedV m) * a) = 0 := by
    have h := congrFun hsol (Fin.last (m + 2))
    rw [hrepr, Matrix.mulVec_add, Pi.add_apply,
      coalescedInverseParticular_final_action,
      coalescedReplacementLimit_final_action] at h
    simpa [coalescedReplacementTarget, Fin.val_last] using h
  have hv := coalescedV_bounds m
  have hlast : (4 - coalescedV m) * b =
      coalescedInverseT m q + (1 - coalescedV m) * a := by
    have hnonzero : coalescedV m / 2 ≠ 0 :=
      ne_of_gt (div_pos hv.1 (by norm_num))
    have hscaled : coalescedV m / 2 *
        (-coalescedInverseT m q +
          ((4 - coalescedV m) * b - (1 - coalescedV m) * a)) = 0 := by
      linear_combination hfinal
    have hinner := (mul_eq_zero.mp hscaled).resolve_left hnonzero
    linarith
  have hfeedback := coalesced_inverse_mode_feedback
    hv.1 hv.2 hmode hlast
  exact ⟨a, b, hrepr, hmode, hlast, hfeedback⟩

end
end PhosphorylationStableCapacity
