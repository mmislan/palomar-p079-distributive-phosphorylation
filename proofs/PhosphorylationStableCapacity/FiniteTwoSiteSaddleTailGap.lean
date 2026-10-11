module
public import proofs.PhosphorylationStableCapacity.FiniteTwoSiteSaddleSpectralCore
public import proofs.PhosphorylationStableCapacity.SaddleSmallGainMatrix
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.NormNum

@[expose] public section
set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

namespace PhosphorylationStableCapacity

noncomputable section

private def saddleBShifted : Matrix (Fin 6) (Fin 6) ℂ :=
  saddleBC - Matrix.scalar (Fin 6) (-2)

private theorem saddleBShifted_row_bound (i : Fin 5) :
    (saddleBShifted i.succ i.succ).re +
      ∑ j ∈ (Finset.univ : Finset (Fin 5)).erase i,
        ‖saddleBShifted i.succ j.succ‖ ≤ -(1 / 2 : ℝ) := by
  fin_cases i <;> norm_num [saddleBShifted, saddleBC, saddleB,
    ScaledIntegerMatrix.realMatrix, Matrix.sub_apply, Matrix.scalar_apply,
    Finset.sum_erase, Fin.sum_univ_succ]

private theorem saddleBShifted_col_bound (i : Fin 5) :
    ‖saddleBShifted i.succ 0‖ ≤ (1 / 100 : ℝ) := by
  fin_cases i <;> norm_num [saddleBShifted, saddleBC, saddleB,
    ScaledIntegerMatrix.realMatrix, Matrix.sub_apply, Matrix.scalar_apply]

private theorem saddleBShifted_feedback_bound :
    (∑ i : Fin 5, ‖saddleBShifted 0 i.succ‖) ≤ (1 / 50 : ℝ) := by
  norm_num [saddleBShifted, saddleBC, saddleB,
    ScaledIntegerMatrix.realMatrix, Matrix.sub_apply, Matrix.scalar_apply,
    Fin.sum_univ_succ]

private theorem saddleBShifted_root_of_root (z : ℂ)
    (hz : saddleBC.charpoly.eval z = 0) :
    saddleBShifted.charpoly.eval (z + 2) = 0 := by
  rw [saddleBShifted, Matrix.charpoly_sub_scalar]
  simpa [Polynomial.eval_comp] using hz

/-- The existing exact rational middle-state similarity certificate localizes
all but its one dominant characteristic root strictly to `Re z < -2`. -/
theorem saddleA1Real_tail_gap :
    ∃ x : ℝ, 0 < x ∧ saddleA1Real.charpoly.IsRoot x ∧
      ((saddleA1Real.map (algebraMap ℝ ℂ)).charpoly).derivative.eval
        (x : ℂ) ≠ 0 ∧
      ∀ z : ℂ,
        z ∈ spectrum ℂ (saddleA1Real.map (algebraMap ℝ ℂ)) →
        z.re < -2 ∨ z = (x : ℂ) := by
  obtain ⟨x, hx, hroot, hsimple⟩ := saddleA1Real_positive_simple_root
  refine ⟨x, hx, hroot, hsimple, ?_⟩
  intro z hz
  by_cases hleft : z.re < -2
  · exact Or.inl hleft
  right
  have hzroot : saddleBC.charpoly.eval z = 0 := by
    rw [saddleBC_charpoly_eq_saddleA1Real]
    exact Matrix.mem_spectrum_iff_isRoot_charpoly.mp hz
  have hxroot : saddleBC.charpoly.eval (x : ℂ) = 0 := by
    rw [saddleBC_charpoly_eq_saddleA1Real, Matrix.charpoly_map]
    have hval :
        (saddleA1Real.charpoly.map (algebraMap ℝ ℂ)).eval (x : ℂ) =
          ((saddleA1Real.charpoly.eval x : ℝ) : ℂ) := by
      simpa using Polynomial.eval_map_apply
        (p := saddleA1Real.charpoly) (f := algebraMap ℝ ℂ) x
    rw [hval]
    exact_mod_cast (by simpa [Polynomial.IsRoot] using hroot :
      saddleA1Real.charpoly.eval x = 0)
  have hunique := block_spectrum_unique_right saddleBShifted
    (1 / 2) (1 / 100) (1 / 50) (1 / 50)
    (by norm_num) saddleBShifted_row_bound saddleBShifted_col_bound
    (by norm_num) (by norm_num) saddleBShifted_feedback_bound
    (by norm_num) (z + 2) ((x : ℂ) + 2)
    (by simp; linarith) (by simp; linarith)
    (saddleBShifted_root_of_root z hzroot)
    (saddleBShifted_root_of_root (x : ℂ) hxroot)
  exact add_right_cancel hunique

end
end PhosphorylationStableCapacity
