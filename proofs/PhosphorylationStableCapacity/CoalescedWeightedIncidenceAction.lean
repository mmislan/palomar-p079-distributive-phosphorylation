module
public import proofs.PhosphorylationStableCapacity.CoalescedWeightedSchurAction
public import proofs.PhosphorylationStableCapacity.CoalescedLoadedIncidenceAction

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section

/-- The weighted slow response is projected incidence of the weighted
finite current vector. -/
theorem coalescedWeightedInverseSlowAction_eq_incidence
    (m : ℕ) (r τ : ℝ) (q : Fin (m + 3) → ℝ) :
    coalescedWeightedInverseSlowAction m r τ q =
      (projectedPathIncidence (m + 2)).mulVec
        (fun i => coalescedFinalCurrentWeights m τ i *
          (coalescedCurrentJacobianMatrix m r).mulVec
            (coalescedInverseResponse m r q) i) := by
  funext j
  simp only [coalescedWeightedInverseSlowAction, Matrix.mulVec,
    dotProduct, projectedPathIncidence, pathIncidence,
    Matrix.transpose_apply, Finset.sum_sub_distrib, sub_mul]
  simp only [ite_mul, one_mul, zero_mul]
  congr 1 <;> (apply Finset.sum_congr rfl; intro i _; simp only [eq_comm])

/-- The physical row weighting is exactly a left diagonal factor on the
finite all-edge loaded current matrix. -/
theorem coalescedWeightedInverseSlowAction_fullEdge
    (m : ℕ) (r τ : ℝ) (z : Fin (m + 2) → ℝ) :
    coalescedWeightedInverseSlowAction m r τ
        ((coalescedFullEdgeForcingMatrix m).mulVec z) =
      r • (projectedPathIncidence (m + 2)).mulVec
        (((Matrix.diagonal (coalescedFinalCurrentWeights m τ)) *
          (coalescedFullLoadedMatrix m r)).mulVec z) := by
  rw [coalescedWeightedInverseSlowAction_eq_incidence]
  have hdiag (v : Fin (m + 2) → ℝ) :
      (fun i => coalescedFinalCurrentWeights m τ i * v i) =
        (Matrix.diagonal (coalescedFinalCurrentWeights m τ)).mulVec v := by
    funext i
    simp [Matrix.mulVec, dotProduct, Matrix.diagonal]
  rw [hdiag]
  unfold coalescedInverseResponse coalescedFullLoadedMatrix
  rw [Matrix.mulVec_smul, Matrix.mulVec_smul, Matrix.mulVec_smul]
  simp only [← Matrix.mulVec_mulVec, Matrix.mul_assoc]

end
end PhosphorylationStableCapacity
