module
public import proofs.PhosphorylationStableCapacity.CoalescedPrefixLoadedMatrix

@[expose] public section

namespace PhosphorylationStableCapacity

open Filter
open scoped Topology

noncomputable section

/-- The exact finite loaded slow-current prefix matrix is Hurwitz for all
sufficiently large positive source parameters. This is the prefix block;
the zero last-edge mode and the fast class-Jacobian spectrum are separate. -/
theorem coalescedPrefixLoadedMatrix_eventually_hurwitz (m : ℕ) :
    ∀ᶠ r : ℝ in atTop, IsHurwitz (coalescedPrefixLoadedMatrix m r) := by
  let w := pathVectorFin (coalescedPathWeights m)
  have hw : ∀ i, 0 < w i :=
    pathVectorFin_pos (coalescedPathWeights m)
      (coalescedPathWeights_pos m)
  have hoff : ∀ᶠ r : ℝ in atTop,
      ∀ i j : Fin (m + 1), i ≠ j →
        0 < coalescedPrefixCurrentMatrix m r i j := by
    suffices h : ∀ᶠ r : ℝ in atTop,
        ∀ i ∈ (Finset.univ : Finset (Fin (m + 1))),
          ∀ j ∈ (Finset.univ : Finset (Fin (m + 1))),
            i ≠ j → 0 < coalescedPrefixCurrentMatrix m r i j by
      simpa using h
    apply (Filter.eventually_all_finset (Finset.univ :
      Finset (Fin (m + 1)))).2
    intro i _
    apply (Filter.eventually_all_finset (Finset.univ :
      Finset (Fin (m + 1)))).2
    intro j _
    by_cases hij : i = j
    · exact Filter.Eventually.of_forall
        (fun _ h => False.elim (h hij))
    · have hlimit : 0 < coalescedYNext m i.val *
          coalescedPathBlock m i j :=
        mul_pos (coalescedYNext_prefix_pos m i)
          (coalescedPath_block_offdiag_pos m i j hij)
      exact ((coalescedPrefixCurrentMatrix_tendsto m i j).eventually
        (isOpen_Ioi.mem_nhds hlimit)).mono (fun _ hp _ => hp)
  have hneg : ∀ᶠ r : ℝ in atTop,
      ∀ i : Fin (m + 1),
        (∑ j, coalescedPrefixCurrentMatrix m r i j * w j) < 0 := by
    suffices h : ∀ᶠ r : ℝ in atTop,
        ∀ i ∈ (Finset.univ : Finset (Fin (m + 1))),
          (∑ j, coalescedPrefixCurrentMatrix m r i j * w j) < 0 by
      simpa using h
    apply (Filter.eventually_all_finset (Finset.univ :
      Finset (Fin (m + 1)))).2
    intro i _
    have hlimit : (∑ j : Fin (m + 1),
        coalescedYNext m i.val * coalescedPathBlock m i j * w j) < 0 := by
      simp_rw [mul_assoc]
      rw [← Finset.mul_sum]
      exact mul_neg_of_pos_of_neg
        (coalescedYNext_prefix_pos m i)
        (coalescedPathBlock_negative_vector m i)
    have hsum : Tendsto (fun r : ℝ =>
        ∑ j : Fin (m + 1),
          coalescedPrefixCurrentMatrix m r i j * w j) atTop
        (𝓝 (∑ j : Fin (m + 1),
          coalescedYNext m i.val *
            coalescedPathBlock m i j * w j)) := by
      apply tendsto_finsetSum
      intro j _
      exact (coalescedPrefixCurrentMatrix_tendsto m i j).mul
        tendsto_const_nhds
    exact hsum.eventually (isOpen_Iio.mem_nhds hlimit)
  filter_upwards [hoff, hneg, eventually_gt_atTop (0 : ℝ)]
    with r hOff hNeg hr
  apply hurwitz_of_metzler_positive_vector
    (coalescedPrefixLoadedMatrix m r) w hw
  · intro i j hij
    have hp := hOff i j hij
    rw [coalescedPrefixCurrentMatrix_eq_r_mul_loaded] at hp
    have hle : 0 ≤ coalescedPrefixLoadedMatrix m r i j := by
      by_contra hn
      have hstrict : coalescedPrefixLoadedMatrix m r i j < 0 :=
        lt_of_not_ge hn
      have hm := mul_neg_of_pos_of_neg hr hstrict
      linarith
    exact hle
  · intro i
    have hp := hNeg i
    have hrow :
        (∑ j : Fin (m + 1),
          coalescedPrefixCurrentMatrix m r i j * w j) =
        r * (∑ j : Fin (m + 1),
          coalescedPrefixLoadedMatrix m r i j * w j) := by
      simp_rw [coalescedPrefixCurrentMatrix_eq_r_mul_loaded,
        mul_assoc]
      rw [Finset.mul_sum]
    rw [hrow] at hp
    by_contra hn
    have hnonneg : 0 ≤ (∑ j : Fin (m + 1),
        coalescedPrefixLoadedMatrix m r i j * w j) :=
      le_of_not_gt hn
    have hm := mul_nonneg hr.le hnonneg
    linarith

end
end PhosphorylationStableCapacity
