module
public import proofs.PhosphorylationStableCapacity.SourceMomentPivotPositive

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section
open PhosphorylationSharpness

theorem sourceLevelC_first_moment {n : ℕ} (x : State n) :
    sourcePathFirstMoment (sourceLevelC x) =
      ∑ i : Fin n, (i.val:ℝ)*x.C i := by
  unfold sourcePathFirstMoment sourceLevelC
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  simp

theorem sourceLevelD_first_moment {n : ℕ} (x : State n) :
    sourcePathFirstMoment (sourceLevelD x) =
      ∑ i : Fin n, ((i.val+1:ℕ):ℝ)*x.D i := by
  unfold sourcePathFirstMoment sourceLevelD
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  simp

theorem sourceOccupancyDifference_first_moment {n : ℕ}
    (x : State n) :
    sourcePathFirstMoment (sourceOccupancyDifference x) =
      (∑ i : Fin n, ((i.val+1:ℕ):ℝ)*x.D i)/totalF x -
      (∑ i : Fin n, (i.val:ℝ)*x.C i)/totalE x := by
  unfold sourcePathFirstMoment sourceOccupancyDifference
  simp_rw [mul_sub]
  simp_rw [← mul_div_assoc]
  rw [Finset.sum_sub_distrib, ← Finset.sum_div, ← Finset.sum_div]
  rw [← sourceLevelD_first_moment, ← sourceLevelC_first_moment]
  rfl

theorem sourceOccupancyDifference_zeroth_moment {n : ℕ}
    (x : State n) :
    sourcePathZerothMoment (sourceOccupancyDifference x) =
      (∑ i : Fin n, x.D i)/totalF x -
      (∑ i : Fin n, x.C i)/totalE x := by
  simp [sourcePathZerothMoment, sourceOccupancyDifference,
    Finset.sum_sub_distrib, ← Finset.sum_div,
    sourceLevelC_sum, sourceLevelD_sum]

theorem sourceOccupancyDifference_affine_moment {n : ℕ}
    (x : State n) (a : ℝ) :
    sourcePathZerothMoment (sourceOccupancyDifference x)*a +
      sourcePathFirstMoment (sourceOccupancyDifference x) =
      (∑ i : Fin n, x.D i*(a+((i.val+1:ℕ):ℝ)))/totalF x -
      (∑ i : Fin n, x.C i*(a+(i.val:ℝ)))/totalE x := by
  rw [sourceOccupancyDifference_zeroth_moment,
    sourceOccupancyDifference_first_moment]
  have hD : (∑ i : Fin n, x.D i*((i.val+1:ℕ):ℝ)) =
      ∑ i : Fin n, ((i.val+1:ℕ):ℝ)*x.D i := by
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hC : (∑ i : Fin n, x.C i*(i.val:ℝ)) =
      ∑ i : Fin n, (i.val:ℝ)*x.C i := by
    apply Finset.sum_congr rfl
    intro i _
    ring
  simp only [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul]
  rw [hD, hC]
  ring

end
end PhosphorylationStableCapacity
