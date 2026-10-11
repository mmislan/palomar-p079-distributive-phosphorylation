module
public import proofs.PhosphorylationStableCapacity.FinalEdgeWeightedBlocks
public import proofs.PhosphorylationStableCapacity.FinalEdgeKernelBlocks

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section

def finalEdgeShearComplement (n : ℕ)
    (K : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (u : Fin (n + 1) → ℝ) (τ : ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  rankOneShearComplement
    (fun i j : Fin n => K i.castSucc j.castSucc)
    (fun i : Fin n => u i.castSucc)
    (fun j : Fin n => K (Fin.last n) j.castSucc) τ

/-- The finite final-column-weighted matrix has an exact zero factor when
its unweighted source has a normalized kernel vector. -/
theorem finalEdgeWeightedMatrix_charpoly_factor (n : ℕ)
    (K : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (u : Fin (n + 1) → ℝ)
    (hulast : u (Fin.last n) = 1) (hKu : K.mulVec u = 0)
    (τ : ℝ) :
    (finalEdgeWeightedMatrix n K τ).charpoly =
      (finalEdgeShearComplement n K u τ).charpoly * Polynomial.X := by
  let A : Matrix (Fin n) (Fin n) ℝ :=
    fun i j => K i.castSucc j.castSucc
  let B : Matrix (Fin n) (Fin 1) ℝ :=
    fun i _ => K i.castSucc (Fin.last n)
  let C : Matrix (Fin 1) (Fin n) ℝ :=
    fun _ j => K (Fin.last n) j.castSucc
  let D : Matrix (Fin 1) (Fin 1) ℝ :=
    fun _ _ => K (Fin.last n) (Fin.last n)
  let U : Matrix (Fin n) (Fin 1) ℝ :=
    fun i _ => u i.castSucc
  have hblocks : A * U + B = 0 ∧ C * U + D = 0 :=
    finalEdgeKernel_block_equations n K u hulast hKu
  have hchar := finalColumnWeightedBlocks_charpoly
    A B C D U τ hblocks.1 hblocks.2
  have hweight := reindex_finalEdgeWeightedMatrix n K τ
  change (finalEdgeWeightedMatrix n K τ).reindex
      (finalEdgeEquiv n).symm (finalEdgeEquiv n).symm =
        finalColumnWeightedBlocks A B C D τ at hweight
  rw [← hweight, Matrix.charpoly_reindex] at hchar
  have hcomp : A - τ • (U * C) = finalEdgeShearComplement n K u τ := by
    ext i j
    change K i.castSucc j.castSucc -
        τ * (∑ k : Fin 1, U i k * C k j) =
      K i.castSucc j.castSucc - τ * u i.castSucc * K (Fin.last n) j.castSucc
    simp only [Fin.sum_univ_one, U, C]
    ring
  rw [hcomp] at hchar
  exact hchar

end
end PhosphorylationStableCapacity
