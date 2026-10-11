module
public import proofs.PhosphorylationStableCapacity.SourceOccupancyMoments

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section
open PhosphorylationSharpness

theorem sourcePath_affine_moment {n : ℕ}
    (t : Fin (n+1) → ℝ) (a : ℝ) :
    sourcePathZerothMoment t*a + sourcePathFirstMoment t =
      ∑ j : Fin (n+1), t j*(a+(j.val:ℝ)) := by
  unfold sourcePathZerothMoment sourcePathFirstMoment
  rw [Finset.sum_mul, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem sourceLevelC_affine_moment {n : ℕ}
    (x : State n) (a : ℝ) :
    (∑ j : Fin (n+1), sourceLevelC x j*(a+(j.val:ℝ))) =
      ∑ i : Fin n, x.C i*(a+(i.val:ℝ)) := by
  rw [← sourcePath_affine_moment,
    sourceLevelC_first_moment]
  change (∑ j : Fin (n+1), sourceLevelC x j)*a +
    (∑ i : Fin n, (i.val:ℝ)*x.C i) = _
  rw [sourceLevelC_sum,
    Finset.sum_mul, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem sourceLevelD_affine_moment {n : ℕ}
    (x : State n) (a : ℝ) :
    (∑ j : Fin (n+1), sourceLevelD x j*(a+(j.val:ℝ))) =
      ∑ i : Fin n, x.D i*(a+((i.val+1:ℕ):ℝ)) := by
  rw [← sourcePath_affine_moment,
    sourceLevelD_first_moment]
  change (∑ j : Fin (n+1), sourceLevelD x j)*a +
    (∑ i : Fin n, ((i.val+1:ℕ):ℝ)*x.D i) = _
  rw [sourceLevelD_sum,
    Finset.sum_mul, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem sourceAugmentedTotalRow_affine_moment {n : ℕ}
    (x : State n) (hx : x.Positive) (a : ℝ) :
    sourcePathZerothMoment (sourceAugmentedTotalRow x)*a +
      sourcePathFirstMoment (sourceAugmentedTotalRow x) =
      (∑ j : Fin (n+1), x.S j*(a+(j.val:ℝ))) +
      x.E/totalE x *
        (∑ i : Fin n, x.C i*(a+(i.val:ℝ))) +
      x.F/totalF x *
        (∑ i : Fin n, x.D i*(a+((i.val+1:ℕ):ℝ))) := by
  have hET : 0 < totalE x := by
    simp [totalE]
    exact add_pos_of_pos_of_nonneg hx.2.1
      (Finset.sum_nonneg fun i _ => (hx.2.2.2.1 i).le)
  have hFT : 0 < totalF x := by
    simp [totalF]
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
      (ne_of_gt hET) (ne_of_gt hFT) j
    simpa [sourceAugmentedTotalRow, totalAndLevelOutputMatrix,
      Matrix.mul_apply] using h
  rw [sourcePath_affine_moment]
  simp_rw [hrow]
  simp only [add_mul, Finset.sum_add_distrib]
  have hCweighted :
      (∑ j : Fin (n+1),
        sourceLevelC x j * x.E / totalE x * (a+(j.val:ℝ))) =
      x.E / totalE x *
        (∑ j : Fin (n+1), sourceLevelC x j*(a+(j.val:ℝ))) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hDweighted :
      (∑ j : Fin (n+1),
        sourceLevelD x j * x.F / totalF x * (a+(j.val:ℝ))) =
      x.F / totalF x *
        (∑ j : Fin (n+1), sourceLevelD x j*(a+(j.val:ℝ))) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [hCweighted, hDweighted,
    sourceLevelC_affine_moment, sourceLevelD_affine_moment]

end
end PhosphorylationStableCapacity
