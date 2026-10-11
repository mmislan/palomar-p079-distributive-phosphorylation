module
public import proofs.PhosphorylationStableCapacity.CoalescedCurrentJacobianMatrix
public import proofs.PhosphorylationStableCapacity.CoalescedPrefixCurrentBlockLimit

@[expose] public section

namespace PhosphorylationStableCapacity

open PhosphorylationSharpness

noncomputable section

/-- The first-prefix incidence-transpose columns in the full substrate-level
space, with zero at the final level. -/
def coalescedPrefixForcingMatrix (m : ℕ) :
    Matrix (Fin (m + 3)) (Fin (m + 1)) ℝ :=
  fun k j => coalescedPrefixEdgeForcing m j k

/-- The exact finite loaded slow-current prefix matrix: current derivative
times inverse loaded mass times incidence-transpose forcing. -/
def coalescedPrefixLoadedMatrix (m : ℕ) (r : ℝ) :
    Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ :=
  fun i j =>
    (coalescedCurrentJacobianMatrix m r *
      (coalescedFullMass m r)⁻¹ *
        coalescedPrefixForcingMatrix m) i.castSucc j

/-- Each finite catalytic-current derivative column is exactly `r` times
the corresponding loaded slow-current matrix entry. -/
theorem coalescedPrefixCurrentMatrix_eq_r_mul_loaded
    (m : ℕ) (r : ℝ) (i j : Fin (m + 1)) :
    coalescedPrefixCurrentMatrix m r i j =
      r * coalescedPrefixLoadedMatrix m r i j := by
  let q := coalescedPrefixEdgeForcing m j
  let e : Fin (m + 1) → ℝ := Pi.single j 1
  have hcolumn : (coalescedPrefixForcingMatrix m).mulVec e = q := by
    funext k
    simp [e, q, coalescedPrefixForcingMatrix]
  have hproduct : coalescedPrefixLoadedMatrix m r i j =
      (coalescedCurrentJacobianMatrix m r).mulVec
        ((coalescedFullMass m r)⁻¹.mulVec q) i.castSucc := by
    unfold coalescedPrefixLoadedMatrix
    calc
      _ = (coalescedCurrentJacobianMatrix m r *
            (coalescedFullMass m r)⁻¹ *
              coalescedPrefixForcingMatrix m).mulVec e i.castSucc := by
        simp [e]
      _ = _ := by
        rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
          hcolumn]
  have hindex : (i.castSucc.succ : Fin (m + 3)) =
      i.succ.castSucc := by
    ext
    rfl
  have haction : coalescedPrefixCurrentMatrix m r i j =
      (coalescedCurrentJacobianMatrix m r).mulVec
        (coalescedInverseResponse m r q) i.castSucc := by
    rw [coalescedCurrentJacobianMatrix_mulVec]
    simp only [coalescedPrefixCurrentMatrix,
      coalescedScaledEdgeCurrent, coalescedInverseFeedback,
      q, hindex]
  calc
    coalescedPrefixCurrentMatrix m r i j =
        (coalescedCurrentJacobianMatrix m r).mulVec
          (r • (coalescedFullMass m r)⁻¹.mulVec q) i.castSucc := by
      rw [haction]
      rfl
    _ = r * (coalescedCurrentJacobianMatrix m r).mulVec
          ((coalescedFullMass m r)⁻¹.mulVec q) i.castSucc := by
      rw [Matrix.mulVec_smul]
      simp only [Pi.smul_apply, smul_eq_mul]
    _ = _ := by rw [hproduct]

end
end PhosphorylationStableCapacity
