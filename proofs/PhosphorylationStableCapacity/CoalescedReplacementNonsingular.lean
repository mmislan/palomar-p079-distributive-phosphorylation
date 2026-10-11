module
public import proofs.PhosphorylationStableCapacity.CoalescedReplacementModeRows
public import proofs.PhosphorylationStableCapacity.RankOneMassRowCompletion
public import proofs.PhosphorylationStableCapacity.CoalescedModeUnique

@[expose] public section
set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

namespace PhosphorylationStableCapacity

noncomputable section

private theorem coalescedFullWeight_restrict_sum (m : ℕ)
    (x : Fin (m + 3) → ℝ) :
    (∑ j : Fin (m + 3), coalescedFullLevelWeight m j * x j) =
      ∑ j : Fin (m + 2), coalescedLevelWeight m j.val * x j.castSucc := by
  rw [Fin.sum_univ_castSucc]
  have hprefix :
      (∑ j : Fin (m + 2),
        coalescedFullLevelWeight m j.castSucc * x j.castSucc) =
      ∑ j : Fin (m + 2), coalescedLevelWeight m j.val * x j.castSucc := by
    apply Finset.sum_congr rfl
    intro j _
    simp [coalescedFullLevelWeight, j.isLt]
  rw [hprefix]
  simp [coalescedFullLevelWeight, Fin.val_last]

/-- The independent leading rows of the limiting replacement matrix force
every occupied coordinate of a kernel vector to have one common value. -/
theorem coalescedReplacementLimit_kernel_occupied_constant (m : ℕ)
    (x : Fin (m + 3) → ℝ)
    (hx : (coalescedReplacementLimit m).mulVec x = 0)
    (i : Fin (m + 2)) :
    x i.castSucc =
      (∑ j : Fin (m + 2), coalescedLevelWeight m j.val * x j.castSucc) / 2 := by
  have hprefix : ∀ k : Fin (m + 1),
      (rankOneMass (fun j : Fin (m + 2) =>
        coalescedLevelWeight m j.val)).mulVec
        (fun j => x j.castSucc) k.castSucc = 0 := by
    intro k
    have hrow := congrFun hx k.castSucc.castSucc
    have hleading :
        (rankOneMass (coalescedFullLevelWeight m)).mulVec x
          k.castSucc.castSucc = 0 := by
      simpa [coalescedReplacementLimit, Matrix.mulVec, dotProduct,
        k.isLt] using hrow
    rw [rankOneMass_action] at hleading ⊢
    rw [coalescedFullWeight_restrict_sum] at hleading
    have hk : k.val < m + 2 := by omega
    simpa [coalescedFullLevelWeight, hk] using hleading
  exact coalescedLeadingMass_prefix_kernel_constant m
    (fun j => x j.castSucc) hprefix i

/-- The limiting replacement matrix has trivial kernel for every number
of sites. The last two rows eliminate the two surviving leading modes. -/
theorem coalescedReplacementLimit_kernel_eq_zero (m : ℕ)
    (x : Fin (m + 3) → ℝ)
    (hx : (coalescedReplacementLimit m).mulVec x = 0) : x = 0 := by
  let a : ℝ :=
    (∑ j : Fin (m + 2), coalescedLevelWeight m j.val * x j.castSucc) / 2
  let b : ℝ := x (Fin.last (m + 2))
  have hrepr : x = coalescedFullKernelVector m a b := by
    funext j
    by_cases hj : j.val < m + 2
    · have heq : j = (⟨j.val, hj⟩ : Fin (m + 2)).castSucc := by
        ext
        rfl
      rw [heq]
      simpa [coalescedFullKernelVector, a, hj] using
        coalescedReplacementLimit_kernel_occupied_constant m x hx
          ⟨j.val, hj⟩
    · have heq : j = Fin.last (m + 2) := by
        ext
        simp [Fin.val_last]
        omega
      rw [heq]
      simp [coalescedFullKernelVector, b, Fin.val_last]
  have hmode :
      (7 - 3 * coalescedV m) * a / 2 +
        3 * coalescedV m * b / 2 = 0 := by
    have h := congrFun hx (coalescedModeRow m)
    rw [hrepr, coalescedReplacementLimit_mode_action] at h
    simpa using h
  have hfinal :
      coalescedV m / 2 *
        ((4 - coalescedV m) * b - (1 - coalescedV m) * a) = 0 := by
    have h := congrFun hx (Fin.last (m + 2))
    rw [hrepr, coalescedReplacementLimit_final_action] at h
    simpa using h
  have hv := coalescedV_bounds m
  have hlast : (4 - coalescedV m) * b = (1 - coalescedV m) * a := by
    have hnonzero : coalescedV m / 2 ≠ 0 :=
      ne_of_gt (div_pos hv.1 (by norm_num))
    exact sub_eq_zero.mp ((mul_eq_zero.mp hfinal).resolve_left hnonzero)
  obtain ⟨ha, hb⟩ := coalesced_mode_homogeneous_unique hv.1 hv.2 hmode hlast
  rw [hrepr, ha, hb]
  funext j
  simp [coalescedFullKernelVector]

theorem coalescedReplacementLimit_det_ne_zero (m : ℕ) :
    (coalescedReplacementLimit m).det ≠ 0 := by
  have hinj : Function.Injective (coalescedReplacementLimit m).mulVec := by
    intro x y hxy
    have hdiff : (coalescedReplacementLimit m).mulVec (x - y) = 0 := by
      rw [Matrix.mulVec_sub, sub_eq_zero]
      exact hxy
    exact sub_eq_zero.mp
      (coalescedReplacementLimit_kernel_eq_zero m (x - y) hdiff)
  exact ((coalescedReplacementLimit m).isUnit_iff_isUnit_det.mp
    (Matrix.mulVec_injective_iff_isUnit.mp hinj)).ne_zero

end
end PhosphorylationStableCapacity
