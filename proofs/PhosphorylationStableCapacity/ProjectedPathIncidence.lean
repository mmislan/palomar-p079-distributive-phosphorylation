module
public import proofs.PhosphorylationStableCapacity.PathIncidence
public import Mathlib.LinearAlgebra.Matrix.Block
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section

/-- Path incidence transpose after discarding the loaded level zero. -/
def projectedPathIncidence (n : ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => (pathIncidence n).transpose i.succ j

theorem projectedPathIncidence_mulVec (n : ℕ) (z : Fin n → ℝ)
    (i : Fin n) :
    (projectedPathIncidence n).mulVec z i =
      (pathIncidence n).transpose.mulVec z i.succ := rfl

/-- The projected incidence matrix is upper triangular. -/
theorem projectedPathIncidence_upperTriangular (n : ℕ) :
    (projectedPathIncidence n).BlockTriangular id := by
  intro i j hji
  change j < i at hji
  have hval : j.val < i.val := hji
  have hsucc : i.succ ≠ j.succ := by
    intro h
    have hv : i.val + 1 = j.val + 1 := by
      simpa only [Fin.val_succ] using congrArg Fin.val h
    omega
  have hcast : i.succ ≠ j.castSucc := by
    intro h
    have hv : i.val + 1 = j.val := by
      simpa only [Fin.val_succ, Fin.val_castSucc] using congrArg Fin.val h
    omega
  simp [projectedPathIncidence, pathIncidence, hsucc, hcast]

/-- Every diagonal entry of the projected incidence matrix is one. -/
theorem projectedPathIncidence_diag (n : ℕ) (i : Fin n) :
    projectedPathIncidence n i i = 1 := by
  have h : i.succ ≠ i.castSucc := by
    intro heq
    have hv := congrArg Fin.val heq
    simp only [Fin.val_succ, Fin.val_castSucc] at hv
    omega
  simp [projectedPathIncidence, pathIncidence, h]

-- The first branch is available only in newer mathlib; the fallback is
-- available in the frozen project. One branch is deliberately unreachable
-- under either individual pin.
set_option linter.unreachableTactic false in
set_option linter.unusedTactic false in
theorem projectedPathIncidence_det (n : ℕ) :
    (projectedPathIncidence n).det = 1 := by
  first
  | rw [Matrix.det_of_isUpperTriangular
      (projectedPathIncidence_upperTriangular n)]
  | rw [Matrix.det_of_upperTriangular
      (projectedPathIncidence_upperTriangular n)]
  simp [projectedPathIncidence_diag]

/-- The edge-to-fixed-total-loaded-coordinate map is invertible at every
system size, including the empty path. -/
theorem projectedPathIncidence_isUnit (n : ℕ) :
    IsUnit (projectedPathIncidence n) := by
  apply (Matrix.isUnit_iff_isUnit_det (projectedPathIncidence n)).mpr
  rw [projectedPathIncidence_det]
  exact isUnit_one

end
end PhosphorylationStableCapacity
