module
public import proofs.PhosphorylationStableCapacity.CoalescedReplacementLimit

@[expose] public section

namespace PhosphorylationStableCapacity

open Filter PhosphorylationSharpness
open scoped Topology

noncomputable section

/-- The limiting phosphatase-complex weights retain the exact unit total. -/
theorem coalescedFullYLimit_sum (m : ℕ) :
    (∑ j : Fin (m + 3), coalescedFullYLimit m j) = 1 := by
  have hlim : Tendsto (fun r : ℝ =>
      ∑ j : Fin (m + 3), coalescedFiniteYLevel m r j) atTop
      (𝓝 (∑ j : Fin (m + 3), coalescedFullYLimit m j)) := by
    apply tendsto_finsetSum
    intro j hj
    exact coalescedFiniteYLevel_tendsto_full_limit m j
  have hconst : Tendsto (fun r : ℝ =>
      ∑ j : Fin (m + 3), coalescedFiniteYLevel m r j) atTop (𝓝 (1 : ℝ)) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [coalescedFiniteState_eventually_component_totals (m + 1)]
      with r h
    rw [coalescedFiniteYLevel_sum, h.2.1]
  exact tendsto_nhds_unique hlim hconst

/-- The limiting substrate weights retain the exact total two. -/
theorem coalescedSubstrateLimit_sum (m : ℕ) :
    (∑ j : Fin (m + 3), coalescedSubstrateLimit (m + 1) j.val) = 2 := by
  have hlim : Tendsto (fun r : ℝ =>
      ∑ j : Fin (m + 3), (coalescedFiniteState (m + 1) r).S j) atTop
      (𝓝 (∑ j : Fin (m + 3),
        coalescedSubstrateLimit (m + 1) j.val)) := by
    apply tendsto_finsetSum
    intro j hj
    exact coalescedFiniteState_S_tendsto (m + 1) j
  have hconst : Tendsto (fun r : ℝ =>
      ∑ j : Fin (m + 3), (coalescedFiniteState (m + 1) r).S j)
      atTop (𝓝 (2 : ℝ)) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [coalescedFiniteState_eventually_component_totals (m + 1)]
      with r h
    exact h.2.2.symm
  exact tendsto_nhds_unique hlim hconst

theorem coalescedFullLevelWeight_sum (m : ℕ) :
    (∑ j : Fin (m + 3), coalescedFullLevelWeight m j) = 2 := by
  rw [Fin.sum_univ_castSucc]
  simp only [coalescedFullLevelWeight, Fin.val_castSucc, Fin.val_last,
    lt_irrefl, ite_false, add_zero]
  have h : (∑ j : Fin (m + 2),
      (if j.val < m + 2 then coalescedLevelWeight m j.val else 0)) =
      ∑ j : Fin (m + 2), coalescedLevelWeight m j.val := by
    apply Finset.sum_congr rfl
    intro j _
    simp [j.isLt]
  rw [h]
  exact (Fin.sum_univ_eq_sum_range (coalescedLevelWeight m) (m + 2)).trans
    (coalescedLevelWeight_mass m)

theorem coalescedFullYLimit_last (m : ℕ) :
    coalescedFullYLimit m (Fin.last (m + 2)) = coalescedV m := by
  simp [coalescedFullYLimit, coalescedV, Fin.val_last]

theorem coalescedSubstrateLimit_last (m : ℕ) :
    coalescedSubstrateLimit (m + 1) (m + 2) = coalescedV m := by
  have hS := coalescedFiniteState_S_tendsto (m + 1)
    (Fin.last (m + 2))
  have hD := coalescedFiniteState_D_tendsto (m + 1)
    (Fin.last (m + 1))
  have heq :
      (fun r : ℝ => (coalescedFiniteState (m + 1) r).S
        (Fin.last (m + 2))) =
      (fun r : ℝ => (coalescedFiniteState (m + 1) r).D
        (Fin.last (m + 1))) := by
    funext r
    exact coalescedFiniteState_lastS_eq_lastD (m + 1) r
  rw [heq] at hS
  have h := tendsto_nhds_unique hS hD
  simpa [coalescedV, coalescedYNext, Fin.val_last] using h

end
end PhosphorylationStableCapacity
