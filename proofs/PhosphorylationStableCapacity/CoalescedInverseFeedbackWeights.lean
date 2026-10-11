module
public import proofs.PhosphorylationStableCapacity.CoalescedInverseModeLimit

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section

theorem coalescedInverseParticular_y_sum (m : ℕ)
    (q : Fin (m + 3) → ℝ) :
    (∑ j : Fin (m + 3), coalescedFullYLimit m j *
      coalescedInverseParticular m q j) = coalescedInverseT m q := by
  rw [Fin.sum_univ_castSucc, coalescedInverseParticular_last]
  simp only [mul_zero, add_zero]
  simp_rw [coalescedInverseParticular_occupied]
  rfl

theorem coalescedFullKernelVector_y_sum (m : ℕ) (a b : ℝ) :
    (∑ j : Fin (m + 3), coalescedFullYLimit m j *
      coalescedFullKernelVector m a b j) =
      (1 - coalescedV m) * a + coalescedV m * b := by
  rw [coalescedFullKernelVector_weighted_sum,
    coalescedFullYLimit_sum, coalescedFullYLimit_last]

theorem coalescedInverseModeVector_y_sum (m : ℕ)
    (q : Fin (m + 3) → ℝ) (a b : ℝ)
    (hlast : (4 - coalescedV m) * b =
      coalescedInverseT m q + (1 - coalescedV m) * a) :
    (∑ j : Fin (m + 3), coalescedFullYLimit m j *
      (coalescedInverseParticular m q +
        coalescedFullKernelVector m a b) j) = 4 * b := by
  simp_rw [Pi.add_apply, mul_add]
  rw [Finset.sum_add_distrib, coalescedInverseParticular_y_sum,
    coalescedFullKernelVector_y_sum]
  linarith

theorem coalescedInverseModeVector_d_sum (m : ℕ)
    (q : Fin (m + 3) → ℝ) (a b : ℝ)
    (hqsum : (∑ j : Fin (m + 3), q j) = 0)
    (hqlast : q (Fin.last (m + 2)) = 0) :
    (∑ j : Fin (m + 3), coalescedFullLevelWeight m j *
      (coalescedInverseParticular m q +
        coalescedFullKernelVector m a b) j) = 2 * a := by
  simp_rw [Pi.add_apply, mul_add]
  rw [Finset.sum_add_distrib,
    coalescedInverseParticular_weighted_sum m q hqsum hqlast,
    coalescedFullKernelVector_mass]
  ring

/-- The source feedback functional of the explicit mode limit is `2b-a`. -/
theorem coalescedInverseModeVector_feedback (m : ℕ)
    (q : Fin (m + 3) → ℝ) (a b : ℝ)
    (hqsum : (∑ j : Fin (m + 3), q j) = 0)
    (hqlast : q (Fin.last (m + 2)) = 0)
    (hlast : (4 - coalescedV m) * b =
      coalescedInverseT m q + (1 - coalescedV m) * a) :
    (∑ j : Fin (m + 3), coalescedFullYLimit m j *
      (coalescedInverseParticular m q +
        coalescedFullKernelVector m a b) j) / 2 -
      (∑ j : Fin (m + 3), coalescedFullLevelWeight m j *
        (coalescedInverseParticular m q +
          coalescedFullKernelVector m a b) j) / 2 =
        2 * b - a := by
  rw [coalescedInverseModeVector_y_sum m q a b hlast,
    coalescedInverseModeVector_d_sum m q a b hqsum hqlast]
  ring

end
end PhosphorylationStableCapacity
