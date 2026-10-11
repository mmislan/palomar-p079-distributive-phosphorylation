module
public import proofs.PhosphorylationStableCapacity.CoalescedFullMassLimit

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section

/-- A full leading-mass kernel vector is constant on every occupied level.
The final, unoccupied level is unconstrained by this leading matrix. -/
theorem coalescedFullMass_kernel_first_constant (m : ℕ)
    (v : Fin (m + 3) → ℝ)
    (hv : (rankOneMass (coalescedFullLevelWeight m)).mulVec v = 0)
    (i : Fin (m + 2)) :
    v i.castSucc =
      (∑ j, coalescedFullLevelWeight m j * v j) / 2 := by
  have h := congrFun hv i.castSucc
  rw [rankOneMass_action] at h
  simp only [Pi.zero_apply] at h
  have hd : 0 < coalescedFullLevelWeight m i.castSucc := by
    simp only [coalescedFullLevelWeight, Fin.val_castSucc]
    simp only [i.isLt, ite_true]
    exact coalescedLevelWeight_pos m i.val (by have := i.isLt; omega)
  exact sub_eq_zero.mp ((mul_eq_zero.mp h).resolve_left (ne_of_gt hd))

/-- A constant value on occupied levels together with an arbitrary final
value describes the two free leading modes. -/
def coalescedFullKernelVector (m : ℕ) (a b : ℝ) : Fin (m + 3) → ℝ :=
  fun i => if i.val < m + 2 then a else b

theorem coalescedFullKernelVector_mass (m : ℕ) (a b : ℝ) :
    (∑ j : Fin (m + 3), coalescedFullLevelWeight m j *
      coalescedFullKernelVector m a b j) = 2 * a := by
  rw [Fin.sum_univ_castSucc]
  simp only [coalescedFullLevelWeight, coalescedFullKernelVector,
    Fin.val_castSucc]
  simp only [Fin.val_last, lt_irrefl, ite_false, zero_mul, add_zero]
  have hterms :
      (∑ j : Fin (m + 2),
        (if j.val < m + 2 then coalescedLevelWeight m j.val else 0) *
          (if j.val < m + 2 then a else b)) =
        ∑ j : Fin (m + 2), coalescedLevelWeight m j.val * a := by
    apply Finset.sum_congr rfl
    intro j _
    simp [j.isLt]
  have hsum : (∑ j : Fin (m + 2), coalescedLevelWeight m j.val) = 2 := by
    exact (Fin.sum_univ_eq_sum_range (coalescedLevelWeight m) (m + 2)).trans
      (coalescedLevelWeight_mass m)
  calc
    (∑ j : Fin (m + 2),
      (if j.val < m + 2 then coalescedLevelWeight m j.val else 0) *
        (if j.val < m + 2 then a else b)) =
        ∑ j : Fin (m + 2), coalescedLevelWeight m j.val * a := hterms
    _ = (∑ j : Fin (m + 2), coalescedLevelWeight m j.val) * a := by
      rw [Finset.sum_mul]
    _ = 2 * a := by rw [hsum]

theorem coalescedFullKernelVector_in_kernel (m : ℕ) (a b : ℝ) :
    (rankOneMass (coalescedFullLevelWeight m)).mulVec
      (coalescedFullKernelVector m a b) = 0 := by
  funext i
  rw [rankOneMass_action, coalescedFullKernelVector_mass]
  simp only [Pi.zero_apply]
  by_cases hi : i.val < m + 2
  · simp [coalescedFullLevelWeight, coalescedFullKernelVector, hi]
  · simp [coalescedFullLevelWeight, hi]

end
end PhosphorylationStableCapacity
