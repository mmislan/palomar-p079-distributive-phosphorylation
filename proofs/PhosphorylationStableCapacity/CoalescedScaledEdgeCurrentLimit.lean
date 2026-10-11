module
public import proofs.PhosphorylationStableCapacity.CoalescedInverseFeedbackCurrentForm

@[expose] public section

namespace PhosphorylationStableCapacity

open Filter PhosphorylationSharpness
open scoped Topology

noncomputable section

/-- The literal first-prefix catalytic-current derivative expression on a
scaled inverse response. Its feedback is exactly the finite common term
of `CoalescedCurrentDerivative`. -/
def coalescedScaledEdgeCurrent (m : ℕ) (r : ℝ)
    (q : Fin (m + 3) → ℝ) (i : Fin (m + 1)) : ℝ :=
  (coalescedFiniteState (m + 1) r).D i.castSucc *
    (coalescedInverseResponse m r q i.castSucc.castSucc -
      coalescedInverseResponse m r q i.succ.castSucc +
        coalescedInverseFeedback m r q)

/-- The scaled edge-current action has the source's expected leading path
difference plus explicit scalar feedback at every first-prefix edge. -/
theorem coalescedScaledEdgeCurrent_tendsto (m : ℕ)
    (q : Fin (m + 3) → ℝ)
    (hqsum : (∑ j : Fin (m + 3), q j) = 0)
    (hqlast : q (Fin.last (m + 2)) = 0)
    (i : Fin (m + 1)) :
    Tendsto (fun r : ℝ => coalescedScaledEdgeCurrent m r q i) atTop
      (𝓝 (coalescedYNext m i.val *
        (q i.castSucc.castSucc / coalescedLevelWeight m i.val -
          q i.succ.castSucc / coalescedLevelWeight m i.succ.val +
          (10 * coalescedInverseT m q +
            (2 + coalescedV m) * coalescedInverseU m q) /
              (2 * (7 - 4 * coalescedV m))))) := by
  obtain ⟨a, b, hresponse, hrow, hlast, hfeedback⟩ :=
    coalescedInverseResponse_explicit_mode_limit m q hqsum hqlast
  have hD : Tendsto (fun r : ℝ =>
      (coalescedFiniteState (m + 1) r).D i.castSucc) atTop
      (𝓝 (coalescedYNext m i.val)) := by
    simpa [coalescedYNext] using
      coalescedFiniteState_D_tendsto (m + 1) i.castSucc
  have hfirst : Tendsto (fun r : ℝ =>
      coalescedInverseResponse m r q i.castSucc.castSucc) atTop
      (𝓝 (q i.castSucc.castSucc / coalescedLevelWeight m i.val + a)) := by
    have hcoord := (tendsto_pi_nhds.mp hresponse) i.castSucc.castSucc
    have hi : i.val < m + 2 := by omega
    have hvalue :
        (coalescedInverseParticular m q +
          coalescedFullKernelVector m a b) i.castSucc.castSucc =
        q i.castSucc.castSucc / coalescedLevelWeight m i.val + a := by
      simp [Pi.add_apply, coalescedInverseParticular_occupied,
        coalescedFullKernelVector, hi]
    rw [hvalue] at hcoord
    exact hcoord
  have hnext : Tendsto (fun r : ℝ =>
      coalescedInverseResponse m r q i.succ.castSucc) atTop
      (𝓝 (q i.succ.castSucc / coalescedLevelWeight m i.succ.val + a)) := by
    have hcoord := (tendsto_pi_nhds.mp hresponse) i.succ.castSucc
    have hvalue :
        (coalescedInverseParticular m q +
          coalescedFullKernelVector m a b) i.succ.castSucc =
        q i.succ.castSucc / coalescedLevelWeight m i.succ.val + a := by
      have hi : i.val + 1 < m + 2 := by omega
      simp [Pi.add_apply, coalescedInverseParticular,
        coalescedFullKernelVector, hi]
    rw [hvalue] at hcoord
    exact hcoord
  have hcommon := coalescedInverseFeedback_tendsto_formula
    m q hqsum hqlast
  have hlimit := hD.mul ((hfirst.sub hnext).add hcommon)
  have hcancel :
      coalescedYNext m i.val *
        (q i.castSucc.castSucc / coalescedLevelWeight m i.val + a -
          (q i.succ.castSucc / coalescedLevelWeight m i.succ.val + a) +
          (10 * coalescedInverseT m q +
            (2 + coalescedV m) * coalescedInverseU m q) /
              (2 * (7 - 4 * coalescedV m))) =
      coalescedYNext m i.val *
        (q i.castSucc.castSucc / coalescedLevelWeight m i.val -
          q i.succ.castSucc / coalescedLevelWeight m i.succ.val +
          (10 * coalescedInverseT m q +
            (2 + coalescedV m) * coalescedInverseU m q) /
              (2 * (7 - 4 * coalescedV m))) := by ring
  rw [hcancel] at hlimit
  simpa only [coalescedScaledEdgeCurrent] using hlimit

end
end PhosphorylationStableCapacity
