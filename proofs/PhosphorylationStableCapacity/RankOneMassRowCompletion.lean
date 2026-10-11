module
public import proofs.PhosphorylationStableCapacity.CoalescedMassKernel

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section

/-- A rank-one mass matrix with total weight two has zero sum of its
output rows. This is the unique row dependence used by the replacement
system for the singular inverse limit. -/
theorem rankOneMass_output_sum_zero {ι : Type*}
    [Fintype ι] [DecidableEq ι]
    (d v : ι → ℝ) (hd : (∑ i, d i) = 2) :
    (∑ i, (rankOneMass d).mulVec v i) = 0 := by
  simp_rw [rankOneMass_action, mul_sub]
  rw [Finset.sum_sub_distrib, ← Finset.sum_mul, hd]
  ring

/-- On the literal coalesced occupied levels, vanishing of the first
`m+1` leading rows forces the omitted final occupied row to vanish. -/
theorem coalescedLeadingMass_prefix_rows_complete
    (m : ℕ) (v : Fin (m + 2) → ℝ)
    (hprefix : ∀ i : Fin (m + 1),
      (rankOneMass (fun j : Fin (m + 2) =>
        coalescedLevelWeight m j)).mulVec v i.castSucc = 0) :
    (rankOneMass (fun j : Fin (m + 2) =>
      coalescedLevelWeight m j)).mulVec v = 0 := by
  let d : Fin (m + 2) → ℝ := fun j => coalescedLevelWeight m j
  have hd : (∑ i : Fin (m + 2), d i) = 2 :=
    (Fin.sum_univ_eq_sum_range (coalescedLevelWeight m) (m + 2)).trans
      (coalescedLevelWeight_mass m)
  have hsum := rankOneMass_output_sum_zero d v hd
  rw [Fin.sum_univ_castSucc] at hsum
  have hprefix_sum :
      (∑ i : Fin (m + 1), (rankOneMass d).mulVec v i.castSucc) = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    exact hprefix i
  rw [hprefix_sum, zero_add] at hsum
  funext i
  by_cases hi : i.val < m + 1
  · have heq : i = (⟨i.val, hi⟩ : Fin (m + 1)).castSucc := by
      ext
      rfl
    rw [heq]
    exact hprefix ⟨i.val, hi⟩
  · have heq : i = Fin.last (m + 1) := by
      ext
      simp [Fin.val_last]
      omega
    rw [heq]
    exact hsum

/-- Therefore a vector annihilated by the independent prefix rows is
constant on all occupied levels. -/
theorem coalescedLeadingMass_prefix_kernel_constant
    (m : ℕ) (v : Fin (m + 2) → ℝ)
    (hprefix : ∀ i : Fin (m + 1),
      (rankOneMass (fun j : Fin (m + 2) =>
        coalescedLevelWeight m j)).mulVec v i.castSucc = 0)
    (i : Fin (m + 2)) :
    v i = (∑ j : Fin (m + 2), coalescedLevelWeight m j * v j) / 2 :=
  coalescedLeadingMass_kernel_constant m v
    (coalescedLeadingMass_prefix_rows_complete m v hprefix) i

end
end PhosphorylationStableCapacity
