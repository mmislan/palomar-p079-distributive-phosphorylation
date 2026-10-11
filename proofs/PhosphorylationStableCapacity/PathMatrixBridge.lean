module
public import Mathlib.Tactic.Ring
public import proofs.PhosphorylationStableCapacity.PathIncidence

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section

/-- The explicit tridiagonal path block is the incidence/weight/incidence
matrix used in the limiting slow dynamics. -/
theorem pathH_eq_incidence {m : ℕ} (d : Fin (m+1) → ℝ) :
    pathH d =
      pathIncidence m * Matrix.diagonal (fun k => (d k)⁻¹) *
        (pathIncidence m).transpose := by
  classical
  ext i j
  simp only [Matrix.mul_apply, Matrix.transpose_apply]
  simp [pathH, pathIncidence, Matrix.diagonal_apply,
    Finset.sum_sub_distrib, sub_mul, mul_sub]
  have hic : i.castSucc.val = i.val := rfl
  have his : i.succ.val = i.val + 1 := rfl
  have hjc : j.castSucc.val = j.val := rfl
  have hjs : j.succ.val = j.val + 1 := rfl
  split_ifs <;> (try omega) <;>
    (clear hic his hjc hjs; simp_all <;> ring)

end
end PhosphorylationStableCapacity
