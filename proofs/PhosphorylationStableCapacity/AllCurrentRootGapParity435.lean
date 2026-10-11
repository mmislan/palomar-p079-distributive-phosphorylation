module
public import proofs.PhosphorylationStableCapacity.SplitScalarIdentity

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section

open PhosphorylationSharpness Polynomial

/-- The bare gap product of the evenly spaced roots alternates sign,
independently of the splitting scale and catalytic currents. -/
theorem nat_offset_root_gap_alternates
    (m : ℕ) (j : Fin (2*m+1)) :
    (Even j.val →
      0 < ∏ i ∈ (Finset.range (2*m+1)).erase j.val,
        ((j.val : ℝ)-(i : ℝ))) ∧
    (Odd j.val →
      (∏ i ∈ (Finset.range (2*m+1)).erase j.val,
        ((j.val : ℝ)-(i : ℝ))) < 0) := by
  have hderiv := splitScalarProduct_deriv_at_root
    m j.val 1 j.isLt
  have hgap :
      (∏ i ∈ (Finset.range (2*m+1)).erase j.val,
        (splitRoot 1 j.val - splitRoot 1 i)) =
      ∏ i ∈ (Finset.range (2*m+1)).erase j.val,
        ((j.val : ℝ)-(i : ℝ)) := by
    apply Finset.prod_congr rfl
    intro i hi
    simp [splitRoot]
  rw [hgap] at hderiv
  have halt := splitScalarProduct_deriv_alternates
    m (by norm_num : (0 : ℝ) < 1) j.val j.isLt
  rw [hderiv] at halt
  exact halt

end

end PhosphorylationStableCapacity
