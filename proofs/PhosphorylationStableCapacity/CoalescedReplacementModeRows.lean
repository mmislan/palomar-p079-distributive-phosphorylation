module
public import proofs.PhosphorylationStableCapacity.CoalescedReplacementSourceTotals
public import proofs.PhosphorylationStableCapacity.CoalescedFullMassKernel

@[expose] public section
set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

namespace PhosphorylationStableCapacity

noncomputable section

/-- A weighted row on the two free leading modes depends only on its total
weight and its final-level weight. -/
theorem coalescedFullKernelVector_weighted_sum (m : ℕ)
    (f : Fin (m + 3) → ℝ) (a b : ℝ) :
    (∑ j : Fin (m + 3), f j * coalescedFullKernelVector m a b j) =
      ((∑ j : Fin (m + 3), f j) - f (Fin.last (m + 2))) * a +
        f (Fin.last (m + 2)) * b := by
  have hprefix :
      (∑ j : Fin (m + 2),
        f j.castSucc * coalescedFullKernelVector m a b j.castSucc) =
      (∑ j : Fin (m + 2), f j.castSucc) * a := by
    simp only [coalescedFullKernelVector, Fin.val_castSucc]
    have h : ∀ j : Fin (m + 2), j.val < m + 2 := fun j => j.isLt
    simp only [h, ite_true]
    rw [Finset.sum_mul]
  have htotal : (∑ j : Fin (m + 3), f j) =
      (∑ j : Fin (m + 2), f j.castSucc) + f (Fin.last (m + 2)) :=
    Fin.sum_univ_castSucc f
  rw [Fin.sum_univ_castSucc, hprefix, htotal]
  simp only [coalescedFullKernelVector, Fin.val_last, lt_irrefl, ite_false]
  ring

private theorem coalescedReplacementModeWeight_sum (m : ℕ) :
    (∑ j : Fin (m + 3),
      (coalescedSubstrateLimit (m + 1) j.val +
        coalescedFullLevelWeight m j / 2 +
          coalescedFullYLimit m j / 2)) = 7 / 2 := by
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
    ← Finset.sum_div, ← Finset.sum_div,
    coalescedSubstrateLimit_sum, coalescedFullLevelWeight_sum,
    coalescedFullYLimit_sum]
  ring

private theorem coalescedReplacementModeWeight_last (m : ℕ) :
    coalescedSubstrateLimit (m + 1) (Fin.last (m + 2)).val +
      coalescedFullLevelWeight m (Fin.last (m + 2)) / 2 +
        coalescedFullYLimit m (Fin.last (m + 2)) / 2 =
      3 * coalescedV m / 2 := by
  rw [Fin.val_last, coalescedSubstrateLimit_last,
    coalescedFullYLimit_last]
  simp [coalescedFullLevelWeight, Fin.val_last]
  ring

/-- The limiting total row on the actual two-mode vectors has the source's
first mode equation. -/
theorem coalescedReplacementLimit_mode_action (m : ℕ) (a b : ℝ) :
    (coalescedReplacementLimit m).mulVec
      (coalescedFullKernelVector m a b) (coalescedModeRow m) =
      (7 - 3 * coalescedV m) * a / 2 +
        3 * coalescedV m * b / 2 := by
  have hrow :
      (coalescedReplacementLimit m).mulVec
        (coalescedFullKernelVector m a b) (coalescedModeRow m) =
      ∑ j : Fin (m + 3),
        (coalescedSubstrateLimit (m + 1) j.val +
          coalescedFullLevelWeight m j / 2 +
            coalescedFullYLimit m j / 2) *
          coalescedFullKernelVector m a b j := by
    simp [Matrix.mulVec, dotProduct, coalescedReplacementLimit,
      coalescedModeRow]
  have h := coalescedFullKernelVector_weighted_sum m
    (fun j => coalescedSubstrateLimit (m + 1) j.val +
      coalescedFullLevelWeight m j / 2 +
        coalescedFullYLimit m j / 2) a b
  rw [coalescedReplacementModeWeight_sum,
    coalescedReplacementModeWeight_last] at h
  rw [hrow, h]
  ring

private theorem coalescedReplacementFinalWeight_sum (m : ℕ) :
    (∑ j : Fin (m + 3),
      ((if Fin.last (m + 2) = j then 2 * coalescedV m else 0) -
        coalescedV m * coalescedFullYLimit m j / 2)) =
      3 * coalescedV m / 2 := by
  rw [Finset.sum_sub_distrib]
  have hdiag :
      (∑ j : Fin (m + 3),
        if Fin.last (m + 2) = j then 2 * coalescedV m else 0) =
        2 * coalescedV m := by
    simp
  rw [hdiag, ← Finset.sum_div, ← Finset.mul_sum,
    coalescedFullYLimit_sum]
  ring

private theorem coalescedReplacementFinalWeight_last (m : ℕ) :
    (if Fin.last (m + 2) = Fin.last (m + 2) then
      2 * coalescedV m else 0) -
        coalescedV m * coalescedFullYLimit m (Fin.last (m + 2)) / 2 =
      2 * coalescedV m - (coalescedV m) ^ 2 / 2 := by
  rw [coalescedFullYLimit_last]
  simp
  ring

/-- The limiting final row on the actual two-mode vectors has the source's
second mode equation. -/
theorem coalescedReplacementLimit_final_action (m : ℕ) (a b : ℝ) :
    (coalescedReplacementLimit m).mulVec
      (coalescedFullKernelVector m a b) (Fin.last (m + 2)) =
      coalescedV m / 2 *
        ((4 - coalescedV m) * b - (1 - coalescedV m) * a) := by
  have hrow :
      (coalescedReplacementLimit m).mulVec
        (coalescedFullKernelVector m a b) (Fin.last (m + 2)) =
      ∑ j : Fin (m + 3),
        ((if Fin.last (m + 2) = j then 2 * coalescedV m else 0) -
          coalescedV m * coalescedFullYLimit m j / 2) *
            coalescedFullKernelVector m a b j := by
    simp [Matrix.mulVec, dotProduct, coalescedReplacementLimit,
      Fin.val_last]
  have h := coalescedFullKernelVector_weighted_sum m
    (fun j => (if Fin.last (m + 2) = j then 2 * coalescedV m else 0) -
      coalescedV m * coalescedFullYLimit m j / 2) a b
  rw [coalescedReplacementFinalWeight_sum,
    coalescedReplacementFinalWeight_last] at h
  rw [hrow, h]
  ring

end
end PhosphorylationStableCapacity
