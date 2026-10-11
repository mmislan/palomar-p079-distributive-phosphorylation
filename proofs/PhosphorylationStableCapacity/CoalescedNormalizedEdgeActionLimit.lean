module
public import proofs.PhosphorylationStableCapacity.CoalescedScaledEdgeCurrentDerivative

@[expose] public section

namespace PhosphorylationStableCapacity

open Filter PhosphorylationSharpness
open scoped Topology

noncomputable section

/-- The edge-coordinate action after factoring out the positive catalytic
current weight from the literal reduced-field derivative. -/
def coalescedNormalizedEdgeAction (m : ℕ) (r : ℝ)
    (q : Fin (m + 3) → ℝ) (i : Fin (m + 1)) : ℝ :=
  coalescedInverseResponse m r q i.castSucc.castSucc -
    coalescedInverseResponse m r q i.succ.castSucc +
      coalescedInverseFeedback m r q

theorem coalescedYNext_prefix_pos (m : ℕ) (i : Fin (m + 1)) :
    0 < coalescedYNext m i.val := by
  unfold coalescedYNext
  exact div_pos
    ((coalescedPair_dense (m + 1)).2.1 i.val (by omega))
    (by positivity)

/-- For every zero-sum direction supported away from the final substrate
level, the normalized first-prefix edge action converges to the path
difference plus the explicit source feedback. -/
theorem coalescedNormalizedEdgeAction_tendsto (m : ℕ)
    (q : Fin (m + 3) → ℝ)
    (hqsum : (∑ j : Fin (m + 3), q j) = 0)
    (hqlast : q (Fin.last (m + 2)) = 0)
    (i : Fin (m + 1)) :
    Tendsto (fun r : ℝ => coalescedNormalizedEdgeAction m r q i) atTop
      (𝓝 (q i.castSucc.castSucc / coalescedLevelWeight m i.val -
          q i.succ.castSucc / coalescedLevelWeight m i.succ.val +
          (10 * coalescedInverseT m q +
            (2 + coalescedV m) * coalescedInverseU m q) /
              (2 * (7 - 4 * coalescedV m)))) := by
  have hD : Tendsto (fun r : ℝ =>
      (coalescedFiniteState (m + 1) r).D i.castSucc) atTop
      (𝓝 (coalescedYNext m i.val)) := by
    simpa [coalescedYNext] using
      coalescedFiniteState_D_tendsto (m + 1) i.castSucc
  have hy : coalescedYNext m i.val ≠ 0 :=
    ne_of_gt (coalescedYNext_prefix_pos m i)
  have hquot :=
    (coalescedScaledEdgeCurrent_tendsto m q hqsum hqlast i).div hD hy
  have hlimit : coalescedYNext m i.val *
        (q i.castSucc.castSucc / coalescedLevelWeight m i.val -
          q i.succ.castSucc / coalescedLevelWeight m i.succ.val +
          (10 * coalescedInverseT m q +
            (2 + coalescedV m) * coalescedInverseU m q) /
              (2 * (7 - 4 * coalescedV m))) /
        coalescedYNext m i.val =
      q i.castSucc.castSucc / coalescedLevelWeight m i.val -
        q i.succ.castSucc / coalescedLevelWeight m i.succ.val +
        (10 * coalescedInverseT m q +
          (2 + coalescedV m) * coalescedInverseU m q) /
            (2 * (7 - 4 * coalescedV m)) := by
    field_simp [hy]
  rw [hlimit] at hquot
  apply hquot.congr'
  filter_upwards [hD.eventually (eventually_ne_nhds hy)] with r hr
  simp [coalescedScaledEdgeCurrent, coalescedNormalizedEdgeAction, hr]

end
end PhosphorylationStableCapacity
