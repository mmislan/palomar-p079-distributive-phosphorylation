module
public import proofs.PhosphorylationStableCapacity.AllCurrentRootGapParity435
public import proofs.PhosphorylationStableCapacity.ArbitrarySplitRootGapNonzero

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section

open PhosphorylationSharpness Polynomial

/-- Strictly ordered arbitrary offsets have the same alternating root-gap
    sign as the evenly spaced offsets. -/
theorem arbitrary_offset_root_gap_alternates
    (m : ℕ) (ξ : ℕ → ℝ) (hξ : StrictMono ξ)
    (j : Fin (2*m+1)) :
    (Even j.val →
      0 < ∏ i ∈ (Finset.range (2*m+1)).erase j.val,
        (ξ j.val-ξ i)) ∧
    (Odd j.val →
      (∏ i ∈ (Finset.range (2*m+1)).erase j.val,
        (ξ j.val-ξ i)) < 0) := by
  let S := (Finset.range (2*m+1)).erase j.val
  let scale : ℕ → ℝ := fun i =>
    (ξ j.val-ξ i)/((j.val : ℝ)-(i : ℝ))
  have hscale (i : ℕ) (hi : i ∈ S) : 0 < scale i := by
    have hij : i ≠ j.val := (Finset.mem_erase.mp hi).1
    rcases lt_or_gt_of_ne hij with hlt | hgt
    · have hξij : ξ i < ξ j.val := hξ hlt
      have hcast : (i : ℝ) < (j.val : ℝ) := by exact_mod_cast hlt
      exact div_pos (sub_pos.mpr hξij) (sub_pos.mpr hcast)
    · have hξji : ξ j.val < ξ i := hξ hgt
      have hcast : (j.val : ℝ) < (i : ℝ) := by exact_mod_cast hgt
      exact div_pos_of_neg_of_neg (sub_neg.mpr hξji)
        (sub_neg.mpr hcast)
  have hscaleprod : 0 < ∏ i ∈ S, scale i := by
    apply Finset.prod_pos
    intro i hi
    exact hscale i hi
  have hgap_eq :
      (∏ i ∈ S, (ξ j.val-ξ i)) =
        (∏ i ∈ S, ((j.val : ℝ)-(i : ℝ))) *
          (∏ i ∈ S, scale i) := by
    calc
      (∏ i ∈ S, (ξ j.val-ξ i)) =
          ∏ i ∈ S, (((j.val : ℝ)-(i : ℝ))*scale i) := by
        apply Finset.prod_congr rfl
        intro i hi
        have hij : j.val ≠ i := (Finset.mem_erase.mp hi).1.symm
        have hden : (j.val : ℝ)-(i : ℝ) ≠ 0 := by
          apply sub_ne_zero.mpr
          intro heq
          exact hij (by exact_mod_cast heq)
        dsimp [scale]
        field_simp [hden]
      _ = _ := by rw [Finset.prod_mul_distrib]
  have hnat := nat_offset_root_gap_alternates m j
  constructor
  · intro heven
    change 0 < ∏ i ∈ S, (ξ j.val-ξ i)
    rw [hgap_eq]
    exact mul_pos (hnat.1 heven) hscaleprod
  · intro hodd
    change (∏ i ∈ S, (ξ j.val-ξ i)) < 0
    rw [hgap_eq]
    exact mul_neg_of_neg_of_pos (hnat.2 hodd) hscaleprod

end
end PhosphorylationStableCapacity
