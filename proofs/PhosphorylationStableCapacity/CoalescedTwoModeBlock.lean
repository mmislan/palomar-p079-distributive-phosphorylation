module
public import proofs.PhosphorylationStableCapacity.CoalescedFullMassKernel

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section

/-- The order-one mass block on the two leading kernel modes in the
ordinary singular-perturbation calculation. `CoalescedFiniteModeBlock`
identifies it as the limit of the literal candidate mass formula's projection;
derivation from the slow-field derivative remains separate. -/
def coalescedTwoModeBlock (v : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![7 / 2 - v - v ^ 2 / 2, v * (v - 1) / 2;
    v * (v - 1) / 2, 2 * v - v ^ 2 / 2]

theorem coalescedTwoModeBlock_det (v : ℝ) :
    (coalescedTwoModeBlock v).det = v * (7 - 4 * v) := by
  simp [coalescedTwoModeBlock, Matrix.det_fin_two]
  ring

theorem coalescedTwoModeBlock_det_pos {v : ℝ} (hv0 : 0 < v) (hv1 : v < 1) :
    0 < (coalescedTwoModeBlock v).det := by
  rw [coalescedTwoModeBlock_det]
  exact mul_pos hv0 (by linarith)

theorem coalescedTwoModeBlock_source_det_pos (m : ℕ) :
    0 < (coalescedTwoModeBlock (coalescedV m)).det := by
  exact coalescedTwoModeBlock_det_pos (coalescedV_bounds m).1
    (coalescedV_bounds m).2

end
end PhosphorylationStableCapacity
