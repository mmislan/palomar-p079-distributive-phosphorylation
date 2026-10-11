module
public import proofs.PhosphorylationStableCapacity.LoadedClassChart

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section

theorem boundComplexAt_add {n : ℕ} (C₁ C₂ D₁ D₂ : Fin n → ℝ)
    (j : Fin (n + 1)) :
    boundComplexAt (C₁ + C₂) (D₁ + D₂) j =
      boundComplexAt C₁ D₁ j + boundComplexAt C₂ D₂ j := by
  classical
  have hC :
      (∑ i : Fin n, if i.castSucc = j then (C₁ + C₂) i else 0) =
        (∑ i : Fin n, if i.castSucc = j then C₁ i else 0) +
        (∑ i : Fin n, if i.castSucc = j then C₂ i else 0) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    by_cases h : i.castSucc = j <;> simp [h]
  have hD :
      (∑ i : Fin n, if i.succ = j then (D₁ + D₂) i else 0) =
        (∑ i : Fin n, if i.succ = j then D₁ i else 0) +
        (∑ i : Fin n, if i.succ = j then D₂ i else 0) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    by_cases h : i.succ = j <;> simp [h]
  unfold boundComplexAt
  rw [hC, hD]
  ring

theorem boundComplexAt_smul {n : ℕ} (a : ℝ) (C D : Fin n → ℝ)
    (j : Fin (n + 1)) :
    boundComplexAt (a • C) (a • D) j =
      a • boundComplexAt C D j := by
  classical
  have hC :
      (∑ i : Fin n, if i.castSucc = j then (a • C) i else 0) =
        a * ∑ i : Fin n, if i.castSucc = j then C i else 0 := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    by_cases h : i.castSucc = j <;> simp [h, smul_eq_mul]
  have hD :
      (∑ i : Fin n, if i.succ = j then (a • D) i else 0) =
        a * ∑ i : Fin n, if i.succ = j then D i else 0 := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    by_cases h : i.succ = j <;> simp [h, smul_eq_mul]
  unfold boundComplexAt
  rw [hC, hD]
  simp only [smul_eq_mul]
  ring

/-- The loaded coordinate change is an invertible linear map, so its
derivative is the same map at every class point. -/
def loadedCoordLinear (n : ℕ) : CoordinateSpace n ≃ₗ[ℝ] CoordinateSpace n :=
  LinearEquiv.ofBijective
    { toFun := toLoadedCoord
      map_add' := by
        intro u v
        apply Prod.ext
        · funext i
          simp [toLoadedCoord, boundComplexAt_add]
          ring
        · rfl
      map_smul' := by
        intro a u
        apply Prod.ext
        · funext i
          simp [toLoadedCoord, boundComplexAt_smul, smul_eq_mul]
          ring
        · rfl }
    (by
      constructor
      · intro u v h
        change toLoadedCoord u = toLoadedCoord v at h
        calc
          u = fromLoadedCoord (toLoadedCoord u) := (from_toLoadedCoord u).symm
          _ = fromLoadedCoord (toLoadedCoord v) := congrArg fromLoadedCoord h
          _ = v := from_toLoadedCoord v
      · intro v
        exact ⟨fromLoadedCoord v, to_fromLoadedCoord v⟩)

@[simp] theorem loadedCoordLinear_apply {n : ℕ} (u : CoordinateSpace n) :
    loadedCoordLinear n u = toLoadedCoord u := rfl

@[simp] theorem loadedCoordLinear_symm_apply {n : ℕ} (u : CoordinateSpace n) :
    (loadedCoordLinear n).symm u = fromLoadedCoord u := by
  apply (loadedCoordLinear n).injective
  simpa only [LinearEquiv.apply_symm_apply, loadedCoordLinear_apply] using
    (to_fromLoadedCoord u).symm

end
end PhosphorylationStableCapacity
