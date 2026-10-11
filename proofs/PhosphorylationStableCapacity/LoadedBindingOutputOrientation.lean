module
public import proofs.PhosphorylationStableCapacity.LoadedBindingTotalPivot

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section
open PhosphorylationSharpness Matrix

/-- Output change from all loaded levels to total loaded inventory followed
by levels `1,...,n`. The first row sums all levels. -/
def totalAndLevelOutputMatrix (n : ℕ) :
    Matrix (Fin (n+1)) (Fin (n+1)) ℝ :=
  fun i j => if i = 0 then 1 else if i = j then 1 else 0

-- The two branches use the lemma names in mathlib 4.35 and 4.30.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
theorem totalAndLevelOutputMatrix_det (n : ℕ) :
    (totalAndLevelOutputMatrix n).det = 1 := by
  have htri : (totalAndLevelOutputMatrix n).BlockTriangular id := by
    intro i j hji
    have hi : i ≠ 0 := by
      intro hi0
      subst i
      exact (not_lt_of_ge (bot_le : (0 : Fin (n+1)) ≤ j)) hji
    have hij : i ≠ j := by
      intro h
      subst j
      exact (lt_irrefl i hji)
    simp [totalAndLevelOutputMatrix, hi, hij]
  first
  | rw [Matrix.det_of_isUpperTriangular htri]
  | rw [Matrix.det_of_upperTriangular htri]
  simp [totalAndLevelOutputMatrix]

theorem totalAndLevelOutputMatrix_mulVec_zero (n : ℕ)
    (v : Fin (n+1) → ℝ) :
    (totalAndLevelOutputMatrix n).mulVec v 0 = ∑ j, v j := by
  simp [totalAndLevelOutputMatrix, Matrix.mulVec, dotProduct]

theorem totalAndLevelOutputMatrix_mulVec_succ (n : ℕ)
    (v : Fin (n+1) → ℝ) (i : Fin n) :
    (totalAndLevelOutputMatrix n).mulVec v i.succ = v i.succ := by
  simp [totalAndLevelOutputMatrix, Matrix.mulVec, dotProduct]

/-- The exact full binding-coordinate output change preserves the
orientation of the physical loaded mass matrix. -/
theorem source_totalAndLevel_bindingMass_det_pos {n : ℕ}
    (x : State n) (hx : x.Positive) :
    0 < ((totalAndLevelOutputMatrix n) *
      loadedBindingMass x.S (sourceLevelC x) (sourceLevelD x)
        (totalE x) (totalF x)).det := by
  rw [Matrix.det_mul, totalAndLevelOutputMatrix_det, one_mul]
  exact source_loadedBindingMass_det_pos x hx

end
end PhosphorylationStableCapacity
