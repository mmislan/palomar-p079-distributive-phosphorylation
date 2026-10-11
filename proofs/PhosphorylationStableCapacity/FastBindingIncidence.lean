module
public import proofs.PhosphorylationStableCapacity.FastBindingEnergy

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section

/-- The loaded-complex incidence map is adjoint to evaluating a level
functional at each complex's occupied level. -/
theorem boundComplexAt_pairing {n : ℕ} (C D : Fin n → ℝ)
    (w : Fin (n + 1) → ℝ) :
    (∑ j, boundComplexAt C D j * w j) =
      (∑ i, C i * w i.castSucc) + (∑ i, D i * w i.succ) := by
  classical
  have hC :
      (∑ j : Fin (n + 1),
          (∑ i : Fin n, if i.castSucc = j then C i else 0) * w j) =
        ∑ i : Fin n, C i * w i.castSucc := by
    simp only [Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    simp
  have hD :
      (∑ j : Fin (n + 1),
          (∑ i : Fin n, if i.succ = j then D i else 0) * w j) =
        ∑ i : Fin n, D i * w i.succ := by
    simp only [Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    simp
  simp only [boundComplexAt, add_mul, Finset.sum_add_distrib]
  rw [hC, hD]

end
end PhosphorylationStableCapacity
