module
public import proofs.PhosphorylationStableCapacity.CoalescedPrefixEdgeForcing
public import proofs.PhosphorylationStableCapacity.CoalescedSpectralGain

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section

/-- For a first-prefix edge column, the first forcing moment is the
difference of the two endpoint phosphatase weights. -/
theorem coalescedPrefixEdgeForcing_T (m : ℕ) (j : Fin (m + 1)) :
    coalescedInverseT m (coalescedPrefixEdgeForcing m j) =
      coalescedFullYLimit m j.succ.castSucc /
          coalescedLevelWeight m j.succ.val -
        coalescedFullYLimit m j.castSucc.castSucc /
          coalescedLevelWeight m j.castSucc.val := by
  calc
    _ = ∑ k : Fin (m + 2),
        (coalescedFullYLimit m k.castSucc /
          coalescedLevelWeight m k.val) *
            coalescedPrefixEdgeForcing m j k.castSucc := by
          unfold coalescedInverseT
          apply Finset.sum_congr rfl
          intro k _
          ring
    _ = _ := coalescedPrefixEdgeForcing_weighted_sum m j _

/-- The shifted forcing moment has the same endpoint-difference form. -/
theorem coalescedPrefixEdgeForcing_U (m : ℕ) (j : Fin (m + 1)) :
    coalescedInverseU m (coalescedPrefixEdgeForcing m j) =
      coalescedYNext m j.succ.val /
          coalescedLevelWeight m j.succ.val -
        coalescedYNext m j.castSucc.val /
          coalescedLevelWeight m j.castSucc.val := by
  calc
    _ = ∑ k : Fin (m + 2),
        (coalescedYNext m k.val /
          coalescedLevelWeight m k.val) *
            coalescedPrefixEdgeForcing m j k.castSucc := by
          unfold coalescedInverseU
          apply Finset.sum_congr rfl
          intro k _
          ring
    _ = _ := coalescedPrefixEdgeForcing_weighted_sum m j _

/-- The explicit feedback from equation (7) for a forcing edge column is
exactly the edge difference of the source's path-feedback vector. -/
theorem coalescedPrefixEdgeForcing_feedback (m : ℕ)
    (j : Fin (m + 1)) :
    (10 * coalescedInverseT m (coalescedPrefixEdgeForcing m j) +
      (2 + coalescedV m) *
        coalescedInverseU m (coalescedPrefixEdgeForcing m j)) /
        (2 * (7 - 4 * coalescedV m)) =
      coalescedPathEdgeFeedback m j := by
  rw [coalescedPrefixEdgeForcing_T, coalescedPrefixEdgeForcing_U]
  have hY (k : Fin (m + 2)) :
      coalescedFullYLimit m k.castSucc =
        coalescedYPrev m k.val := by
    rfl
  rw [hY j.succ, hY j.castSucc]
  unfold coalescedPathEdgeFeedback
  rw [pathIncidence_mulVec]
  have hlevel (k : Fin (m + 2)) :
      (10 * (coalescedYPrev m k.val /
          coalescedLevelWeight m k.val) +
        (2 + coalescedV m) * (coalescedYNext m k.val /
          coalescedLevelWeight m k.val)) /
        (2 * (7 - 4 * coalescedV m)) =
          coalescedPathFeedback m k := by
    change _ = (10 * coalescedYPrev m k.val +
      (2 + coalescedV m) * coalescedYNext m k.val) /
        (2 * (7 - 4 * coalescedV m) *
          coalescedLevelWeight m k.val)
    calc
      _ = ((10 * coalescedYPrev m k.val +
          (2 + coalescedV m) * coalescedYNext m k.val) /
            coalescedLevelWeight m k.val) /
          (2 * (7 - 4 * coalescedV m)) := by
            congr 1
            rw [add_div, mul_div_assoc', mul_div_assoc']
      _ = _ := by
        rw [← div_mul_eq_div_div]
        congr 1
        ac_rfl
  calc
    _ = (10 * (coalescedYPrev m j.succ.val /
            coalescedLevelWeight m j.succ.val) +
          (2 + coalescedV m) * (coalescedYNext m j.succ.val /
            coalescedLevelWeight m j.succ.val)) /
            (2 * (7 - 4 * coalescedV m)) -
        (10 * (coalescedYPrev m j.castSucc.val /
            coalescedLevelWeight m j.castSucc.val) +
          (2 + coalescedV m) * (coalescedYNext m j.castSucc.val /
            coalescedLevelWeight m j.castSucc.val)) /
            (2 * (7 - 4 * coalescedV m)) := by
              have hnum :
                  10 * (coalescedYPrev m j.succ.val /
                      coalescedLevelWeight m j.succ.val -
                    coalescedYPrev m j.castSucc.val /
                      coalescedLevelWeight m j.castSucc.val) +
                    (2 + coalescedV m) *
                      (coalescedYNext m j.succ.val /
                          coalescedLevelWeight m j.succ.val -
                        coalescedYNext m j.castSucc.val /
                          coalescedLevelWeight m j.castSucc.val) =
                    (10 * (coalescedYPrev m j.succ.val /
                        coalescedLevelWeight m j.succ.val) +
                      (2 + coalescedV m) *
                        (coalescedYNext m j.succ.val /
                          coalescedLevelWeight m j.succ.val)) -
                    (10 * (coalescedYPrev m j.castSucc.val /
                        coalescedLevelWeight m j.castSucc.val) +
                      (2 + coalescedV m) *
                        (coalescedYNext m j.castSucc.val /
                          coalescedLevelWeight m j.castSucc.val)) := by
                rw [mul_sub, mul_sub]
                abel
              rw [hnum, sub_div]
    _ = _ := by rw [hlevel j.succ, hlevel j.castSucc]

end
end PhosphorylationStableCapacity
