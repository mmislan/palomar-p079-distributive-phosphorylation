module
public import proofs.PhosphorylationStableCapacity.CoalescedAllEdgeDeterminant

@[expose] public section

namespace PhosphorylationStableCapacity

open Filter

noncomputable section

/-- Weight the final catalytic current by `τ`, leaving every prefix current
weight equal to one. -/
def coalescedFinalCurrentWeights (m : ℕ) (τ : ℝ) (j : Fin (m + 2)) : ℝ :=
  if j = Fin.last (m + 1) then τ else 1

/-- The complete loaded slow-current matrix with a separately adjustable
final catalytic-current weight. -/
def coalescedFinalWeightedMatrix (m : ℕ) (r τ : ℝ) :
    Matrix (Fin (m + 2)) (Fin (m + 2)) ℝ :=
  coalescedFullLoadedMatrix m r *
    Matrix.diagonal (coalescedFinalCurrentWeights m τ)

theorem coalescedFinalWeightedMatrix_apply (m : ℕ) (r τ : ℝ)
    (i j : Fin (m + 2)) :
    coalescedFinalWeightedMatrix m r τ i j =
      coalescedFullLoadedMatrix m r i j *
        coalescedFinalCurrentWeights m τ j := by
  simp [coalescedFinalWeightedMatrix, Matrix.mul_diagonal]

theorem coalescedFinalWeightedMatrix_prefix (m : ℕ) (r τ : ℝ)
    (i j : Fin (m + 1)) :
    coalescedFinalWeightedMatrix m r τ i.castSucc j.castSucc =
      coalescedPrefixLoadedMatrix m r i j := by
  rw [coalescedFinalWeightedMatrix_apply,
    coalescedFullLoadedMatrix_prefix]
  simp [coalescedFinalCurrentWeights]

theorem coalescedFinalWeightedMatrix_last_zero (m : ℕ) (r : ℝ)
    (i : Fin (m + 2)) :
    coalescedFinalWeightedMatrix m r 0 i (Fin.last (m + 1)) = 0 := by
  rw [coalescedFinalWeightedMatrix_apply]
  simp [coalescedFinalCurrentWeights]

/-- Exact singularity persists for every final-current weight, including
positive weights. -/
theorem coalescedFinalWeightedMatrix_eventually_det_eq_zero (m : ℕ) :
    ∀ᶠ r : ℝ in atTop, ∀ τ : ℝ,
      (coalescedFinalWeightedMatrix m r τ).det = 0 := by
  filter_upwards [coalescedFullLoadedMatrix_eventually_det_eq_zero m]
    with r hdet τ
  simp [coalescedFinalWeightedMatrix, Matrix.det_mul, hdet]

end
end PhosphorylationStableCapacity
