module
public import proofs.PhosphorylationStableCapacity.AllCurrentSchurAction435
public import proofs.PhosphorylationStableCapacity.CoalescedLoadedIncidenceAction

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section

/-- The weighted slow response is projected incidence of the weighted
finite current vector. -/
theorem coalescedAllInverseSlowAction_eq_incidence
    (m : ℕ) (r : ℝ) (w : Fin (m + 2) → ℝ) (q : Fin (m + 3) → ℝ) :
    coalescedAllInverseSlowAction m r w q =
      (projectedPathIncidence (m + 2)).mulVec
        (fun i => w i *
          (coalescedCurrentJacobianMatrix m r).mulVec
            (coalescedInverseResponse m r q) i) := by
  funext j
  simp only [coalescedAllInverseSlowAction, Matrix.mulVec,
    dotProduct, projectedPathIncidence, pathIncidence,
    Matrix.transpose_apply, Finset.sum_sub_distrib, sub_mul]
  simp only [ite_mul, one_mul, zero_mul]
  congr 1 <;> (apply Finset.sum_congr rfl; intro i _; simp only [eq_comm])

/-- The physical row weighting is exactly a left diagonal factor on the
finite all-edge loaded current matrix. -/
theorem coalescedAllInverseSlowAction_fullEdge
    (m : ℕ) (r : ℝ) (w : Fin (m + 2) → ℝ) (z : Fin (m + 2) → ℝ) :
    coalescedAllInverseSlowAction m r w
        ((coalescedFullEdgeForcingMatrix m).mulVec z) =
      r • (projectedPathIncidence (m + 2)).mulVec
        (((Matrix.diagonal (w)) *
          (coalescedFullLoadedMatrix m r)).mulVec z) := by
  rw [coalescedAllInverseSlowAction_eq_incidence]
  have hdiag (v : Fin (m + 2) → ℝ) :
      (fun i => w i * v i) =
        (Matrix.diagonal (w)).mulVec v := by
    funext i
    simp [Matrix.mulVec, dotProduct, Matrix.diagonal]
  rw [hdiag]
  unfold coalescedInverseResponse coalescedFullLoadedMatrix
  rw [Matrix.mulVec_smul, Matrix.mulVec_smul, Matrix.mulVec_smul]
  simp only [← Matrix.mulVec_mulVec, Matrix.mul_assoc]

end
end PhosphorylationStableCapacity
