module
public import proofs.PhosphorylationStableCapacity.CoalescedPrefixEdgeFeedback
public import proofs.PhosphorylationStableCapacity.PathMatrixBridge

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section

/-- The two local inverse-response coordinates for an edge forcing column
are the negative of the path matrix entry. -/
theorem coalescedPrefixEdgeForcing_pathH (m : ℕ)
    (i j : Fin (m + 1)) :
    coalescedPrefixEdgeForcing m j i.castSucc.castSucc /
        coalescedLevelWeight m i.castSucc.val -
      coalescedPrefixEdgeForcing m j i.succ.castSucc /
        coalescedLevelWeight m i.succ.val =
          -pathH (coalescedPathWeights m) i j := by
  let e : Fin (m + 1) → ℝ := Pi.single j 1
  have hcolumn (k : Fin (m + 2)) :
      (pathIncidence (m + 1)).transpose.mulVec e k =
        coalescedPrefixEdgeForcing m j k.castSucc := by
    rw [Matrix.mulVec_single_one]
    rw [coalescedPrefixEdgeForcing_occupied]
    rfl
  have hdiag :
      (Matrix.diagonal (fun k : Fin (m + 2) =>
        (coalescedPathWeights m k)⁻¹)).mulVec
          ((pathIncidence (m + 1)).transpose.mulVec e) =
        (fun k : Fin (m + 2) =>
          coalescedPrefixEdgeForcing m j k.castSucc /
            coalescedPathWeights m k) := by
    funext k
    rw [Matrix.mulVec_diagonal, hcolumn]
    ring
  have hH : pathH (coalescedPathWeights m) i j =
      coalescedPrefixEdgeForcing m j i.succ.castSucc /
          coalescedPathWeights m i.succ -
        coalescedPrefixEdgeForcing m j i.castSucc.castSucc /
          coalescedPathWeights m i.castSucc := by
    calc
      _ = (pathH (coalescedPathWeights m)).mulVec e i := by
        simp [e]
      _ = (pathIncidence (m + 1)).mulVec
          ((Matrix.diagonal (fun k : Fin (m + 2) =>
            (coalescedPathWeights m k)⁻¹)).mulVec
              ((pathIncidence (m + 1)).transpose.mulVec e)) i := by
        rw [pathH_eq_incidence, ← Matrix.mulVec_mulVec,
          ← Matrix.mulVec_mulVec]
      _ = _ := by
        rw [hdiag, pathIncidence_mulVec]
  rw [hH]
  simp only [coalescedPathWeights]
  ring

end
end PhosphorylationStableCapacity
