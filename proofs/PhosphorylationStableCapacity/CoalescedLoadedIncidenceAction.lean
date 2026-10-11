module
public import proofs.PhosphorylationStableCapacity.CoalescedLoadedSchurAction
public import proofs.PhosphorylationStableCapacity.ProjectedPathIncidence
public import proofs.PhosphorylationStableCapacity.CoalescedFullLoadedMatrix

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section

/-- The explicit loaded slow action is the projected incidence of the
finite current response. -/
theorem coalescedInverseSlowAction_eq_incidence (m : ℕ) (r : ℝ)
    (q : Fin (m + 3) → ℝ) :
    coalescedInverseSlowAction m r q =
      (projectedPathIncidence (m + 2)).mulVec
        ((coalescedCurrentJacobianMatrix m r).mulVec
          (coalescedInverseResponse m r q)) := by
  funext j
  simp only [coalescedInverseSlowAction, Matrix.mulVec, dotProduct,
    projectedPathIncidence, pathIncidence, Matrix.transpose_apply,
    Finset.sum_sub_distrib, sub_mul]
  simp only [ite_mul, one_mul, zero_mul]
  congr 1 <;> (apply Finset.sum_congr rfl; intro i _; simp only [eq_comm])

/-- The edge forcing has exactly the projected incidence as its loaded
nonzero-level rows. -/
theorem coalescedFullEdgeForcing_succ (m : ℕ)
    (z : Fin (m + 2) → ℝ) (i : Fin (m + 2)) :
    (coalescedFullEdgeForcingMatrix m).mulVec z i.succ =
      (projectedPathIncidence (m + 2)).mulVec z i := rfl

theorem coalescedFullEdgeForcing_eq_pathIncidence (m : ℕ) :
    coalescedFullEdgeForcingMatrix m =
      (pathIncidence (m + 2)).transpose := rfl

/-- Every edge forcing conserves total loaded substrate. -/
theorem coalescedFullEdgeForcing_sum_zero (m : ℕ)
    (z : Fin (m + 2) → ℝ) :
    (∑ k : Fin (m + 3),
      (coalescedFullEdgeForcingMatrix m).mulVec z k) = 0 := by
  rw [coalescedFullEdgeForcing_eq_pathIncidence]
  simp_rw [pathIncidence_transpose_mulVec_sums]
  rw [Finset.sum_sub_distrib]
  have hleft :
      (∑ k : Fin (m + 3), ∑ i : Fin (m + 2),
        if k = i.succ then z i else 0) = ∑ i : Fin (m + 2), z i := by
    rw [Finset.sum_comm]
    simp
  have hright :
      (∑ k : Fin (m + 3), ∑ i : Fin (m + 2),
        if k = i.castSucc then z i else 0) = ∑ i : Fin (m + 2), z i := by
    rw [Finset.sum_comm]
    simp
  rw [hleft, hright, sub_self]

theorem coalescedBindingCoordTangent_fullEdge_slow (m : ℕ) (r : ℝ)
    (z : Fin (m + 2) → ℝ) :
    (coalescedBindingCoordTangent m r
      ((coalescedFullEdgeForcingMatrix m).mulVec z)).1 =
        r • (projectedPathIncidence (m + 2)).mulVec z := by
  funext i
  simp only [coalescedBindingCoordTangent, Pi.smul_apply, smul_eq_mul]
  rw [coalescedFullEdgeForcing_succ]

/-- On incidence edge forcing, the exact source slow response is the
projected incidence of the finite loaded current matrix, scaled by r. -/
theorem coalescedInverseSlowAction_fullEdge (m : ℕ) (r : ℝ)
    (z : Fin (m + 2) → ℝ) :
    coalescedInverseSlowAction m r
        ((coalescedFullEdgeForcingMatrix m).mulVec z) =
      r • (projectedPathIncidence (m + 2)).mulVec
        ((coalescedFullLoadedMatrix m r).mulVec z) := by
  rw [coalescedInverseSlowAction_eq_incidence]
  unfold coalescedInverseResponse coalescedFullLoadedMatrix
  rw [Matrix.mulVec_smul, Matrix.mulVec_smul,
    Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
  simp only [← Matrix.mulVec_mulVec, Matrix.mul_assoc]

end
end PhosphorylationStableCapacity
