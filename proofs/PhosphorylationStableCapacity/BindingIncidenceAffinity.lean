module
public import proofs.PhosphorylationStableCapacity.BindingIncidenceCovariance

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section
open Matrix
open scoped BigOperators

theorem diagonal_mulVec_function
    {ι : Type*} [Fintype ι] [DecidableEq ι] (d v : ι → ℝ) :
    diagonal d *ᵥ v = fun i => d i * v i := by
  ext i
  exact mulVec_diagonal d v i

theorem inverse_diagonal_of_entries_ne_zero
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (w : ι → ℝ) (hw : ∀ i, w i ≠ 0) :
    (diagonal w)⁻¹ = diagonal (fun i => (w i)⁻¹) := by
  apply inv_eq_right_inv
  rw [diagonal_mul_diagonal]
  ext i j
  by_cases hij : i = j
  · subst j
    simp [hw i]
  · simp [hij]

theorem bindingFreeIncidence_mulVec
    {ι ℓ : Type*} [Fintype ι] [DecidableEq ℓ]
    (p q : ι → ℓ) (v w : ι → ℝ) :
    bindingFreeIncidence p q *ᵥ Sum.elim v w =
      Sum.elim
        (fun j => bindingLevelInventory p v j + bindingLevelInventory q w j)
        ![∑ i, v i, ∑ i, w i] := by
  ext a
  cases a with
  | inl j =>
    simp [Matrix.mulVec, dotProduct, bindingFreeIncidence,
      Fintype.sum_sum_type, bindingLevelInventory]
  | inr j =>
    fin_cases j <;>
      simp [Matrix.mulVec, dotProduct, bindingFreeIncidence, Fintype.sum_sum_type]

theorem bindingFreeIncidence_transpose_mulVec
    {ι ℓ : Type*} [Fintype ℓ] [DecidableEq ℓ]
    (p q : ι → ℓ) (σ : ℓ → ℝ) (e f : ℝ) :
    (bindingFreeIncidence p q).transpose *ᵥ Sum.elim σ ![e, f] =
      Sum.elim (fun i => σ (p i) + e) (fun i => σ (q i) + f) := by
  ext a
  cases a with
  | inl i =>
    simp [Matrix.mulVec, dotProduct, bindingFreeIncidence,
      Fintype.sum_sum_type]
  | inr i =>
    simp [Matrix.mulVec, dotProduct, bindingFreeIncidence,
      Fintype.sum_sum_type]

/-- The complementary Hessian is exactly the sum of each complex's
own affinity, its occupied substrate affinity and its enzyme affinity. -/
theorem binding_affinity_action
    {ι ℓ : Type*} [Fintype ι] [Fintype ℓ]
    [DecidableEq ι] [DecidableEq ℓ]
    (p q : ι → ℓ) (S : ℓ → ℝ) (C Y : ι → ℝ) (E F : ℝ)
    (v w : ι → ℝ) :
    let K := bindingFreeIncidence p q
    let Hi := diagonal (fun a => (Sum.elim C Y a)⁻¹) +
      K.transpose * diagonal (fun a => (Sum.elim S ![E, F] a)⁻¹) * K
    Hi *ᵥ Sum.elim v w =
      Sum.elim
        (fun i => v i / C i +
          (bindingLevelInventory p v (p i) + bindingLevelInventory q w (p i)) / S (p i) +
          (∑ j, v j) / E)
        (fun i => w i / Y i +
          (bindingLevelInventory p v (q i) + bindingLevelInventory q w (q i)) / S (q i) +
          (∑ j, w j) / F) := by
  dsimp only
  rw [Matrix.add_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    bindingFreeIncidence_mulVec]
  simp_rw [diagonal_mulVec_function]
  have hfree :
      (fun a => (Sum.elim S ![E, F] a)⁻¹ *
        Sum.elim
          (fun j => bindingLevelInventory p v j + bindingLevelInventory q w j)
          ![∑ i, v i, ∑ i, w i] a) =
        Sum.elim
          (fun j => (bindingLevelInventory p v j + bindingLevelInventory q w j) / S j)
          ![(∑ i, v i) / E, (∑ i, w i) / F] := by
    ext a
    cases a with
    | inl j => simp [div_eq_mul_inv, mul_comm]
    | inr j => fin_cases j <;> simp [div_eq_mul_inv, mul_comm]
  rw [hfree, bindingFreeIncidence_transpose_mulVec]
  ext a
  cases a with
  | inl i => simp [div_eq_mul_inv, mul_comm, add_assoc]
  | inr i => simp [div_eq_mul_inv, mul_comm, add_assoc]

end
end PhosphorylationStableCapacity
