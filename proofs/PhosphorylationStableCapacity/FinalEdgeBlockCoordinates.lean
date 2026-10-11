module
public import proofs.PhosphorylationStableCapacity.RankOneBlockSimilarity

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section

/-- Split a finite edge path into its leading edges and final edge. -/
def finalEdgeEquiv (n : ℕ) : (Fin n ⊕ Fin 1) ≃ Fin (n + 1) :=
  finSumFinEquiv

@[simp] theorem finalEdgeEquiv_inl (n : ℕ) (i : Fin n) :
    finalEdgeEquiv n (Sum.inl i) = i.castSucc := by
  rfl

@[simp] theorem finalEdgeEquiv_inr (n : ℕ) (j : Fin 1) :
    finalEdgeEquiv n (Sum.inr j) = Fin.last n := by
  fin_cases j
  rfl

/-- Reindexing a finite path matrix by the prefix/final-edge split gives its
four literal blocks. -/
theorem reindex_finalEdgeEquiv_fromBlocks (n : ℕ)
    (K : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) :
    K.reindex (finalEdgeEquiv n).symm (finalEdgeEquiv n).symm =
      Matrix.fromBlocks
        (fun i j : Fin n => K i.castSucc j.castSucc)
        (fun (i : Fin n) (_ : Fin 1) => K i.castSucc (Fin.last n))
        (fun (_ : Fin 1) (j : Fin n) => K (Fin.last n) j.castSucc)
        (fun (_ _ : Fin 1) => K (Fin.last n) (Fin.last n)) := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    simp [Matrix.reindex_apply, Matrix.fromBlocks]

end
end PhosphorylationStableCapacity
