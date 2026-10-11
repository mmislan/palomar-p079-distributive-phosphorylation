module
public import proofs.PhosphorylationStableCapacity.CoalescedSourceShiftIdentity

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section

/-- The explicit particular solution of the leading singular mass equation.
The last substrate coordinate is zero. -/
def coalescedInverseParticular (m : ℕ)
    (q : Fin (m + 3) → ℝ) : Fin (m + 3) → ℝ :=
  fun j => if j.val < m + 2 then
    q j / coalescedLevelWeight m j.val else 0

theorem coalescedInverseParticular_occupied (m : ℕ)
    (q : Fin (m + 3) → ℝ) (j : Fin (m + 2)) :
    coalescedInverseParticular m q j.castSucc =
      q j.castSucc / coalescedLevelWeight m j.val := by
  simp [coalescedInverseParticular, j.isLt]

theorem coalescedInverseParticular_last (m : ℕ)
    (q : Fin (m + 3) → ℝ) :
    coalescedInverseParticular m q (Fin.last (m + 2)) = 0 := by
  simp [coalescedInverseParticular, Fin.val_last]

/-- Zero total forcing cancels the rank-one correction in the leading mass
matrix when the particular vector is divided by the source level weights. -/
theorem coalescedInverseParticular_weighted_sum (m : ℕ)
    (q : Fin (m + 3) → ℝ)
    (hqsum : (∑ i : Fin (m + 3), q i) = 0)
    (hqlast : q (Fin.last (m + 2)) = 0) :
    (∑ j : Fin (m + 3),
      coalescedFullLevelWeight m j * coalescedInverseParticular m q j) = 0 := by
  have hocc : (∑ j : Fin (m + 2), q j.castSucc) = 0 := by
    rw [Fin.sum_univ_castSucc, hqlast, add_zero] at hqsum
    exact hqsum
  rw [Fin.sum_univ_castSucc]
  have hterms :
      (∑ j : Fin (m + 2), coalescedFullLevelWeight m j.castSucc *
        coalescedInverseParticular m q j.castSucc) =
      ∑ j : Fin (m + 2), q j.castSucc := by
    apply Finset.sum_congr rfl
    intro j _
    rw [coalescedInverseParticular_occupied]
    have hd : coalescedLevelWeight m j.val ≠ 0 :=
      ne_of_gt (coalescedLevelWeight_pos m j.val (by omega))
    simp [coalescedFullLevelWeight, j.isLt]
    field_simp [hd]
  rw [hterms, hocc]
  simp [coalescedFullLevelWeight, Fin.val_last]

/-- The leading mass matrix maps the particular vector to each occupied
forcing coordinate. -/
theorem coalescedInverseParticular_leading_action (m : ℕ)
    (q : Fin (m + 3) → ℝ)
    (hqsum : (∑ i : Fin (m + 3), q i) = 0)
    (hqlast : q (Fin.last (m + 2)) = 0)
    (i : Fin (m + 2)) :
    (rankOneMass (coalescedFullLevelWeight m)).mulVec
      (coalescedInverseParticular m q) i.castSucc = q i.castSucc := by
  rw [rankOneMass_action,
    coalescedInverseParticular_weighted_sum m q hqsum hqlast,
    zero_div, sub_zero, coalescedInverseParticular_occupied]
  have hd : coalescedLevelWeight m i.val ≠ 0 :=
    ne_of_gt (coalescedLevelWeight_pos m i.val (by omega))
  simp [coalescedFullLevelWeight, i.isLt]
  field_simp [hd]

end
end PhosphorylationStableCapacity
