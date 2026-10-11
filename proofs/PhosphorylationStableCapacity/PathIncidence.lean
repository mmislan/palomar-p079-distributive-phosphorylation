module
public import Mathlib.Data.Matrix.Mul
public import proofs.PhosphorylationStableCapacity.PathLaplacian

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section

/-- The edge-by-level incidence matrix of a finite path, with edge `i`
oriented from level `i` to level `i+1`. -/
def pathIncidence (m : ℕ) : Matrix (Fin m) (Fin (m+1)) ℝ :=
  fun i k => (if k = i.succ then 1 else 0) -
    (if k = i.castSucc then 1 else 0)

/-- Incidence takes adjacent differences of a level vector. -/
theorem pathIncidence_mulVec {m : ℕ} (q : Fin (m+1) → ℝ)
    (i : Fin m) :
    (pathIncidence m).mulVec q i = q i.succ - q i.castSucc := by
  simp [Matrix.mulVec, dotProduct, pathIncidence,
    Finset.sum_sub_distrib, sub_mul]

end
end PhosphorylationStableCapacity
