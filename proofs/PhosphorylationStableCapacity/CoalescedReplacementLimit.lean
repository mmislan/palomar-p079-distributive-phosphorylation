module
public import proofs.PhosphorylationStableCapacity.CoalescedReplacementRows

@[expose] public section

namespace PhosphorylationStableCapacity

open Filter PhosphorylationSharpness
open scoped Topology

noncomputable section

/-- The limiting phosphatase-complex concentration on every substrate
level, including the empty first level. -/
def coalescedFullYLimit (m : ℕ) (j : Fin (m + 3)) : ℝ :=
  if j.val = 0 then 0 else coalescedYNext m (j.val - 1)

/-- The proposed entrywise limit of the literal square row-replacement
matrix. Its first rows are the leading rank-one mass matrix, followed by
the finite total and final mode rows. -/
def coalescedReplacementLimit (m : ℕ) :
    Matrix (Fin (m + 3)) (Fin (m + 3)) ℝ :=
  fun i j =>
    if i.val < m + 1 then
      rankOneMass (coalescedFullLevelWeight m) i j
    else if i.val = m + 1 then
      coalescedSubstrateLimit (m + 1) j.val +
        coalescedFullLevelWeight m j / 2 +
          coalescedFullYLimit m j / 2
    else
      (if Fin.last (m + 2) = j then 2 * coalescedV m else 0) -
        coalescedV m * coalescedFullYLimit m j / 2

theorem coalescedFiniteYLevel_tendsto_full_limit
    (m : ℕ) (j : Fin (m + 3)) :
    Tendsto (fun r : ℝ => coalescedFiniteYLevel m r j) atTop
      (𝓝 (coalescedFullYLimit m j)) := by
  simpa only [coalescedFullYLimit] using
    coalescedFiniteYLevel_tendsto m j

theorem coalescedFiniteYLevel_last_tendsto_v (m : ℕ) :
    Tendsto (fun r : ℝ =>
      coalescedFiniteYLevel m r (Fin.last (m + 2))) atTop
      (𝓝 (coalescedV m)) := by
  have h := coalescedFiniteState_D_tendsto (m + 1) (Fin.last (m + 1))
  simpa [coalescedFiniteYLevel_last, coalescedV, coalescedYNext]
    using h

/-- Exact source totals and the established component limits identify the
finite replacement system's total row in the large-parameter limit. -/
theorem coalescedReplacementMass_mode_row_tendsto
    (m : ℕ) (j : Fin (m + 3)) :
    Tendsto (fun r : ℝ =>
      coalescedReplacementMass m r (coalescedModeRow m) j) atTop
      (𝓝 (coalescedSubstrateLimit (m + 1) j.val +
        coalescedFullLevelWeight m j / 2 +
          coalescedFullYLimit m j / 2)) := by
  have hS := coalescedFiniteState_S_tendsto (m + 1) j
  have hC := coalescedFiniteCLevel_scaled_tendsto m j
  have hY := coalescedFiniteYLevel_tendsto_full_limit m j
  have hCshare : Tendsto
      (fun r : ℝ => coalescedFiniteCLevel m r j / (2 * r)) atTop
      (𝓝 (coalescedFullLevelWeight m j / 2)) := by
    apply (hC.div_const 2).congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with r hr
    field_simp [ne_of_gt hr]
  have hlim := (hS.add hCshare).add (hY.div_const 2)
  apply hlim.congr'
  filter_upwards [coalescedFiniteState_eventually_component_totals (m + 1),
    eventually_gt_atTop (0 : ℝ)] with r htot hr
  exact (coalescedReplacementMass_mode_row_formula m r j
    (ne_of_gt hr) htot.1 htot.2.1).symm

/-- The final replacement row has an ordinary finite limit determined by
the top phosphatase weight and all level weights. -/
theorem coalescedReplacementMass_final_row_tendsto
    (m : ℕ) (j : Fin (m + 3)) :
    Tendsto (fun r : ℝ =>
      coalescedReplacementMass m r (Fin.last (m + 2)) j) atTop
      (𝓝 ((if Fin.last (m + 2) = j then 2 * coalescedV m else 0) -
        coalescedV m * coalescedFullYLimit m j / 2)) := by
  have hv := coalescedFiniteYLevel_last_tendsto_v m
  have hY := coalescedFiniteYLevel_tendsto_full_limit m j
  have hdiag : Tendsto
      (fun r : ℝ => if Fin.last (m + 2) = j then
        2 * coalescedFiniteYLevel m r (Fin.last (m + 2)) else 0)
      atTop (𝓝 (if Fin.last (m + 2) = j then
        2 * coalescedV m else 0)) := by
    by_cases hj : Fin.last (m + 2) = j
    · simpa [hj] using (tendsto_const_nhds.mul hv :
        Tendsto (fun r : ℝ => (2 : ℝ) *
          coalescedFiniteYLevel m r (Fin.last (m + 2))) atTop
          (𝓝 (2 * coalescedV m)))
    · simp [hj]
  have hlim := hdiag.sub ((hv.mul hY).div_const 2)
  apply hlim.congr'
  filter_upwards [] with r
  exact (coalescedReplacementMass_final_row_formula m r j).symm

/-- The actual finite square replacement matrix converges entrywise to
its source-specific limit for every number of sites. -/
theorem coalescedReplacementMass_tendsto
    (m : ℕ) (i j : Fin (m + 3)) :
    Tendsto (fun r : ℝ => coalescedReplacementMass m r i j) atTop
      (𝓝 (coalescedReplacementLimit m i j)) := by
  by_cases hi : i.val < m + 1
  · have h := coalescedFullMassScaled_tendsto m i j
    have hscaled : Tendsto
        (fun r : ℝ => coalescedReplacementMass m r i j) atTop
        (𝓝 (rankOneMass (coalescedFullLevelWeight m) i j)) := by
      apply h.congr'
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with r hr
      simp only [coalescedReplacementMass, hi, ite_true]
      exact coalescedFullMassScaled_eq m (ne_of_gt hr) i j
    simpa [coalescedReplacementLimit, hi] using hscaled
  · by_cases hm : i.val = m + 1
    · have heq : i = coalescedModeRow m := by
        ext
        exact hm
      rw [heq]
      simpa [coalescedReplacementLimit, coalescedModeRow] using
        coalescedReplacementMass_mode_row_tendsto m j
    · have heq : i = Fin.last (m + 2) := by
        ext
        simp [Fin.val_last]
        omega
      rw [heq]
      simpa [coalescedReplacementLimit, Fin.val_last] using
        coalescedReplacementMass_final_row_tendsto m j

end
end PhosphorylationStableCapacity
