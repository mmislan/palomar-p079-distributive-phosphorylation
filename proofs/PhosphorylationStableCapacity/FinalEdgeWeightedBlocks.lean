module
public import proofs.PhosphorylationStableCapacity.FinalEdgeBlockCoordinates

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section

def finalEdgeWeights (n : ℕ) (τ : ℝ) (j : Fin (n + 1)) : ℝ :=
  if j = Fin.last n then τ else 1

def finalEdgeWeightedMatrix (n : ℕ)
    (K : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (τ : ℝ) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
  K * Matrix.diagonal (finalEdgeWeights n τ)

section

-- The two mathlib pins discharge the final scalar-action cases at different
-- simplification stages; the remaining `rfl` is needed on the newer pin.
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

/-- The literal final-column weighting is exactly the four-block weighting
used by the triangular similarity theorem. -/
theorem reindex_finalEdgeWeightedMatrix (n : ℕ)
    (K : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (τ : ℝ) :
    (finalEdgeWeightedMatrix n K τ).reindex
      (finalEdgeEquiv n).symm (finalEdgeEquiv n).symm =
      finalColumnWeightedBlocks
        (fun i j : Fin n => K i.castSucc j.castSucc)
        (fun (i : Fin n) (_ : Fin 1) => K i.castSucc (Fin.last n))
        (fun (_ : Fin 1) (j : Fin n) => K (Fin.last n) j.castSucc)
        (fun (_ _ : Fin 1) => K (Fin.last n) (Fin.last n)) τ := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    simp [finalEdgeWeightedMatrix, finalEdgeWeights,
      finalColumnWeightedBlocks, Matrix.fromBlocks,
      Matrix.reindex_apply, Matrix.mul_diagonal, mul_comm] <;> rfl

end

end
end PhosphorylationStableCapacity
