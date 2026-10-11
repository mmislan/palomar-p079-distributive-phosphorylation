module
public import proofs.PhosphorylationStableCapacity.CoalescedInverseOccupiedFormula

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section

/-- The first forcing moment in the manuscript's equation (6). -/
def coalescedInverseT (m : ℕ) (q : Fin (m + 3) → ℝ) : ℝ :=
  ∑ j : Fin (m + 2), coalescedFullYLimit m j.castSucc *
    (q j.castSucc / coalescedLevelWeight m j.val)

/-- The shifted forcing moment in the manuscript's equation (6). -/
def coalescedInverseU (m : ℕ) (q : Fin (m + 3) → ℝ) : ℝ :=
  ∑ j : Fin (m + 2), coalescedYNext m j.val *
    (q j.castSucc / coalescedLevelWeight m j.val)

theorem coalescedInverseParticular_mode_action (m : ℕ)
    (q : Fin (m + 3) → ℝ)
    (hqsum : (∑ j : Fin (m + 3), q j) = 0)
    (hqlast : q (Fin.last (m + 2)) = 0) :
    (coalescedReplacementLimit m).mulVec
      (coalescedInverseParticular m q) (coalescedModeRow m) =
      3 * coalescedInverseT m q / 2 + coalescedInverseU m q := by
  have hqocc : (∑ j : Fin (m + 2), q j.castSucc) = 0 := by
    rw [Fin.sum_univ_castSucc, hqlast, add_zero] at hqsum
    exact hqsum
  have hrow :
      (coalescedReplacementLimit m).mulVec
        (coalescedInverseParticular m q) (coalescedModeRow m) =
      ∑ j : Fin (m + 3),
        (coalescedSubstrateLimit (m + 1) j.val +
          coalescedFullLevelWeight m j / 2 +
            coalescedFullYLimit m j / 2) *
          coalescedInverseParticular m q j := by
    simp [Matrix.mulVec, dotProduct, coalescedReplacementLimit,
      coalescedModeRow]
  rw [hrow, Fin.sum_univ_castSucc,
    coalescedInverseParticular_last]
  simp only [mul_zero, add_zero]
  have hterms :
      (∑ j : Fin (m + 2),
        (coalescedSubstrateLimit (m + 1) j.castSucc.val +
          coalescedFullLevelWeight m j.castSucc / 2 +
            coalescedFullYLimit m j.castSucc / 2) *
          coalescedInverseParticular m q j.castSucc) =
      ∑ j : Fin (m + 2),
        (3 * coalescedFullYLimit m j.castSucc *
            (q j.castSucc / coalescedLevelWeight m j.val) / 2 +
          coalescedYNext m j.val *
            (q j.castSucc / coalescedLevelWeight m j.val) +
          q j.castSucc / 2) := by
    apply Finset.sum_congr rfl
    intro j _
    rw [coalescedInverseParticular_occupied]
    simp only [Fin.val_castSucc]
    rw [coalescedSubstrateLimit_adjacent_y]
    have hd : coalescedLevelWeight m j.val ≠ 0 :=
      ne_of_gt (coalescedLevelWeight_pos m j.val (by omega))
    simp only [coalescedFullLevelWeight, Fin.val_castSucc]
    simp only [j.isLt, ite_true]
    field_simp [hd]
    ring
  rw [hterms, Finset.sum_add_distrib, Finset.sum_add_distrib]
  simp only [coalescedInverseT, coalescedInverseU]
  have hthird : (∑ j : Fin (m + 2), q j.castSucc / 2) = 0 := by
    rw [← Finset.sum_div, hqocc]
    norm_num
  rw [hthird]
  have hfirst :
      (∑ j : Fin (m + 2),
        3 * coalescedFullYLimit m j.castSucc *
          (q j.castSucc / coalescedLevelWeight m j.val) / 2) =
      3 * (∑ j : Fin (m + 2),
        coalescedFullYLimit m j.castSucc *
          (q j.castSucc / coalescedLevelWeight m j.val)) / 2 := by
    rw [← Finset.sum_div]
    congr 1
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [hfirst]
  ring

theorem coalescedInverseParticular_final_action (m : ℕ)
    (q : Fin (m + 3) → ℝ) :
    (coalescedReplacementLimit m).mulVec
      (coalescedInverseParticular m q) (Fin.last (m + 2)) =
      -coalescedV m * coalescedInverseT m q / 2 := by
  have hrow :
      (coalescedReplacementLimit m).mulVec
        (coalescedInverseParticular m q) (Fin.last (m + 2)) =
      ∑ j : Fin (m + 3),
        ((if Fin.last (m + 2) = j then 2 * coalescedV m else 0) -
          coalescedV m * coalescedFullYLimit m j / 2) *
            coalescedInverseParticular m q j := by
    simp [Matrix.mulVec, dotProduct, coalescedReplacementLimit,
      Fin.val_last]
  rw [hrow, Fin.sum_univ_castSucc,
    coalescedInverseParticular_last]
  simp only [mul_zero, add_zero]
  have hterms :
      (∑ j : Fin (m + 2),
        ((if Fin.last (m + 2) = j.castSucc then 2 * coalescedV m else 0) -
          coalescedV m * coalescedFullYLimit m j.castSucc / 2) *
            coalescedInverseParticular m q j.castSucc) =
      ∑ j : Fin (m + 2),
        -coalescedV m *
          (coalescedFullYLimit m j.castSucc *
            (q j.castSucc / coalescedLevelWeight m j.val)) / 2 := by
    apply Finset.sum_congr rfl
    intro j _
    have hne : Fin.last (m + 2) ≠ j.castSucc := by
      intro h
      have hv := congrArg Fin.val h
      simp at hv
      omega
    simp [hne, coalescedInverseParticular_occupied]
    ring
  rw [hterms, ← Finset.sum_div, ← Finset.mul_sum]
  simp only [coalescedInverseT]

end
end PhosphorylationStableCapacity
