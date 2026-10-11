module
public import proofs.PhosphorylationStableCapacity.CoalescedFeedbackMoment

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section

def coalescedPathWeights (m : ℕ) : Fin ((m + 1) + 1) → ℝ :=
  fun i => coalescedLevelWeight m i.val

def coalescedPathFeedback (m : ℕ) : Fin ((m + 1) + 1) → ℝ :=
  fun i => coalescedFeedbackLevel m i.val

theorem coalescedPathWeights_pos (m : ℕ) (i : Fin ((m + 1) + 1)) :
    0 < coalescedPathWeights m i := by
  exact coalescedLevelWeight_pos m i.val (by have := i.isLt; omega)

theorem coalescedPathWeights_mean (m : ℕ) :
    pathMean (m + 1) (pathWeightsNat (coalescedPathWeights m)) =
      coalescedMu m := by
  have hindex : (m + 1) + 1 = m + 2 := by omega
  have hnat (k : ℕ) (hk : k ∈ Finset.range (m + 2)) :
      pathWeightsNat (coalescedPathWeights m) k =
        coalescedLevelWeight m k := by
    have hlt : k < (m + 1) + 1 := by
      have := Finset.mem_range.mp hk
      omega
    simp [pathWeightsNat, coalescedPathWeights, hlt]
  have hnum :
      (∑ k ∈ Finset.range (m + 2),
        pathWeightsNat (coalescedPathWeights m) k * (k : ℝ)) =
      (∑ k ∈ Finset.range (m + 2),
        coalescedLevelWeight m k * (k : ℝ)) := by
    apply Finset.sum_congr rfl
    intro k hk
    rw [hnat k hk]
  have hden :
      (∑ k ∈ Finset.range (m + 2),
        pathWeightsNat (coalescedPathWeights m) k) =
      (∑ k ∈ Finset.range (m + 2), coalescedLevelWeight m k) := by
    apply Finset.sum_congr rfl
    exact hnat
  unfold pathMean
  rw [hindex, hnum, hden]
  exact coalescedPathMean m

theorem coalescedPathFeedback_fin_moment (m : ℕ) :
    (∑ i : Fin ((m + 1) + 1),
      coalescedPathFeedback m i * coalescedPathWeights m i *
        ((i.val : ℝ) - coalescedMu m)) =
      (10 * (4 / 3 - coalescedV m *
        (((m : ℝ) + 2) - coalescedMu m)) +
          (2 + coalescedV m) / 3) / (14 - 8 * coalescedV m) := by
  let f : ℕ → ℝ := fun i =>
    coalescedFeedbackLevel m i * coalescedLevelWeight m i *
      ((i : ℝ) - coalescedMu m)
  have hfin := Fin.sum_univ_eq_sum_range f ((m + 1) + 1)
  have hindex : (m + 1) + 1 = m + 2 := by omega
  change (∑ i : Fin ((m + 1) + 1), f i.val) = _
  rw [hfin, hindex]
  exact coalescedFeedbackLevel_moment m

/-- The source-specific scalar gain on the explicit positive path vector.
Only the edge-feedback sign and literal-matrix limit remain outside this
finite gain identity. -/
theorem coalescedPath_feedback_gain (m : ℕ) :
    (∑ i,
      (pathIncidence (m + 1)).mulVec (coalescedPathFeedback m) i *
        pathVectorFin (coalescedPathWeights m) i) =
      (10 * (4 / 3 - coalescedV m *
        (((m : ℝ) + 2) - coalescedMu m)) +
          (2 + coalescedV m) / 3) / (14 - 8 * coalescedV m) := by
  have hm : 0 < m + 1 := by omega
  have hd : ∀ i, 0 < coalescedPathWeights m i :=
    coalescedPathWeights_pos m
  calc
    (∑ i,
      (pathIncidence (m + 1)).mulVec (coalescedPathFeedback m) i *
        pathVectorFin (coalescedPathWeights m) i) =
      ∑ k, coalescedPathFeedback m k * coalescedPathWeights m k *
        ((k.val : ℝ) -
          pathMean (m + 1) (pathWeightsNat (coalescedPathWeights m))) :=
        path_feedback_gain_eq_moment hm (coalescedPathWeights m) hd
          (coalescedPathFeedback m)
    _ = _ := by
      rw [coalescedPathWeights_mean]
      exact coalescedPathFeedback_fin_moment m

end
end PhosphorylationStableCapacity
