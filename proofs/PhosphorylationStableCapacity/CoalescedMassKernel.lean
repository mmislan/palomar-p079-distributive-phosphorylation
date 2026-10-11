module
public import proofs.PhosphorylationStableCapacity.CoalescedLoadedMassLimit
public import proofs.PhosphorylationStableCapacity.RankOneMassKernel

@[expose] public section

namespace PhosphorylationStableCapacity

open Filter
open scoped Topology

noncomputable section

/-- The leading first-level mass limit is the generic diagonal-minus-rank-one
matrix whose kernel is exactly the constant mode. -/
theorem coalescedLoadedMassScaled_tendsto_rankOneMass (m : ℕ)
    (i j : Fin (m + 2)) :
    Tendsto (fun r : ℝ => coalescedLoadedMassScaled m r i j) atTop
      (𝓝 (rankOneMass (fun k : Fin (m + 2) =>
        coalescedLevelWeight m k) i j)) := by
  simpa only [rankOneMass] using coalescedLoadedMassScaled_tendsto m i j

theorem coalescedLeadingMass_kernel_constant (m : ℕ)
    (v : Fin (m + 2) → ℝ)
    (hv : (rankOneMass (fun k : Fin (m + 2) =>
      coalescedLevelWeight m k)).mulVec v = 0)
    (i : Fin (m + 2)) :
    v i = (∑ j : Fin (m + 2), coalescedLevelWeight m j * v j) / 2 := by
  exact rankOneMass_kernel_constant
    (fun k : Fin (m + 2) => coalescedLevelWeight m k) v
    (fun k => coalescedLevelWeight_pos m k (by have := k.isLt; omega)) hv i

theorem coalescedLeadingMass_constant_kernel (m : ℕ) (a : ℝ) :
    (rankOneMass (fun k : Fin (m + 2) =>
      coalescedLevelWeight m k)).mulVec (fun _ => a) = 0 := by
  have hsum : (∑ i : Fin (m + 2), coalescedLevelWeight m i) = 2 := by
    exact (Fin.sum_univ_eq_sum_range (coalescedLevelWeight m) (m + 2)).trans
      (coalescedLevelWeight_mass m)
  exact rankOneMass_constant_kernel
    (fun k : Fin (m + 2) => coalescedLevelWeight m k) hsum a

end
end PhosphorylationStableCapacity
