module
public import proofs.PhosphorylationStableCapacity.CoalescedFiniteSource
public import proofs.PhosphorylationStableCapacity.CoalescedYMoments

@[expose] public section

namespace PhosphorylationStableCapacity

open Filter
open scoped Topology

noncomputable section

/-- The literal finite-parameter phosphatase complex tends to the source
path's normalized `y_(i+1)` coefficient. -/
theorem coalescedFinite_D_to_path (m : ℕ) (i : Fin (m + 2)) :
    Tendsto (fun r : ℝ => (coalescedFiniteState (m + 1) r).D i)
      atTop (𝓝 (coalescedYNext m i)) := by
  simpa only [coalescedYNext] using
    coalescedFiniteState_D_tendsto (m + 1) i

/-- The literal kinase complex divided by `r` tends to the exact positive
path level weight `d_i`. -/
theorem coalescedFinite_C_scaled_to_path (m : ℕ) (i : Fin (m + 2)) :
    Tendsto (fun r : ℝ => (coalescedFiniteState (m + 1) r).C i / r)
      atTop (𝓝 (coalescedLevelWeight m i)) := by
  simpa only [coalescedLevelWeight] using
    coalescedFiniteState_C_scaled_tendsto (m + 1) i

end
end PhosphorylationStableCapacity
