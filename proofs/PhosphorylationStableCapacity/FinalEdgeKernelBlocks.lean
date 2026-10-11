module
public import proofs.PhosphorylationStableCapacity.FinalEdgeBlockCoordinates

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section

def finalEdgeLeadingBlock (n : ℕ)
    (K : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  fun i j => K i.castSucc j.castSucc

def finalEdgeTopRightBlock (n : ℕ)
    (K : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) :
    Matrix (Fin n) (Fin 1) ℝ :=
  fun i _ => K i.castSucc (Fin.last n)

def finalEdgeLastRowBlock (n : ℕ)
    (K : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) :
    Matrix (Fin 1) (Fin n) ℝ :=
  fun _ j => K (Fin.last n) j.castSucc

def finalEdgeBottomRightBlock (n : ℕ)
    (K : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) :
    Matrix (Fin 1) (Fin 1) ℝ :=
  fun _ _ => K (Fin.last n) (Fin.last n)

def finalEdgeKernelColumn (n : ℕ)
    (u : Fin (n + 1) → ℝ) : Matrix (Fin n) (Fin 1) ℝ :=
  fun i _ => u i.castSucc

/-- A full finite kernel vector normalized at the final edge supplies the
two block equations needed by the triangular similarity theorem. -/
theorem finalEdgeKernel_block_equations (n : ℕ)
    (K : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (u : Fin (n + 1) → ℝ)
    (hulast : u (Fin.last n) = 1) (hKu : K.mulVec u = 0) :
    finalEdgeLeadingBlock n K * finalEdgeKernelColumn n u +
      finalEdgeTopRightBlock n K = 0 ∧
    finalEdgeLastRowBlock n K * finalEdgeKernelColumn n u +
      finalEdgeBottomRightBlock n K = 0 := by
  constructor
  · ext i j
    fin_cases j
    have hi : K.mulVec u i.castSucc = 0 := congrFun hKu i.castSucc
    simpa [finalEdgeLeadingBlock, finalEdgeKernelColumn,
      finalEdgeTopRightBlock, Matrix.mul_apply, Matrix.mulVec, dotProduct,
      Fin.sum_univ_castSucc, hulast] using hi
  · ext i j
    fin_cases i
    fin_cases j
    have hi : K.mulVec u (Fin.last n) = 0 := congrFun hKu (Fin.last n)
    simpa [finalEdgeLastRowBlock, finalEdgeKernelColumn,
      finalEdgeBottomRightBlock, Matrix.mul_apply, Matrix.mulVec, dotProduct,
      Fin.sum_univ_castSucc, hulast] using hi

end
end PhosphorylationStableCapacity
