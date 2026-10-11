module
public import Mathlib.Basic.Real.Basic
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.Data.Fin.Basic
public import Mathlib.Tactic.SplitIfs

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section

/-- The path matrix `R₀ diag(1/d) R₀ᵀ` on the first `m+1` slow levels,
written in edge coordinates. Edge `i` joins levels `i` and `i+1`. -/
def pathH {m : ℕ} (d : Fin (m+1) → ℝ) : Matrix (Fin m) (Fin m) ℝ :=
  fun i j =>
    if i = j then (d i.castSucc)⁻¹ + (d i.succ)⁻¹
    else if i.succ = j.castSucc then -(d i.succ)⁻¹
    else if j.succ = i.castSucc then -(d j.succ)⁻¹
    else 0

theorem pathH_diag_pos {m : ℕ} (d : Fin (m+1) → ℝ)
    (hd : ∀ i, 0 < d i) (i : Fin m) : 0 < pathH d i i := by
  simp only [pathH]
  exact add_pos (inv_pos.mpr (hd i.castSucc)) (inv_pos.mpr (hd i.succ))

theorem pathH_offdiag_nonpos {m : ℕ} (d : Fin (m+1) → ℝ)
    (hd : ∀ i, 0 < d i) (i j : Fin m) (hij : i ≠ j) :
    pathH d i j ≤ 0 := by
  unfold pathH
  simp only [hij, ite_false]
  split_ifs
  · exact neg_nonpos.mpr (le_of_lt (inv_pos.mpr (hd _)))
  · exact neg_nonpos.mpr (le_of_lt (inv_pos.mpr (hd _)))
  · exact le_refl 0

end
end PhosphorylationStableCapacity
