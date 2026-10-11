module
public import proofs.PhosphorylationStableCapacity.CoalescedJStrictLogConcavity

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section

theorem coalescedPrevRatio_eq_coeff (m i : ℕ)
    (hi : 0 < i) (him : i ≤ m + 1) :
    coalescedPrevRatio m i =
      (coalescedPair (m + 1)).2.coeff (i - 1) /
        (coalescedPair (m + 1)).2.coeff i := by
  have hzero : i ≠ 0 := by omega
  have hden : (36 : ℝ) ^ (m + 1) ≠ 0 := by positivity
  have hJi : (coalescedPair (m + 1)).2.coeff i ≠ 0 :=
    ne_of_gt ((coalescedPair_dense (m + 1)).2.1 i him)
  unfold coalescedPrevRatio coalescedYPrev
  simp only [hzero, ↓reduceIte]
  unfold coalescedYNext
  field_simp [hden, hJi]

/-- The first ratio premise in the conditional coalesced path theorem is
now unconditional for the literal source at every level. -/
theorem coalescedPrevRatio_strict_mono (m : ℕ) :
    ∀ i ≤ m,
      coalescedPrevRatio m i < coalescedPrevRatio m (i + 1) := by
  intro i hi
  by_cases hzero : i = 0
  · subst i
    rw [coalescedPrevRatio_eq_coeff m 1 (by omega) (by omega)]
    have hd := (coalescedPair_dense (m + 1)).2
    have hpos : 0 < (coalescedPair (m + 1)).2.coeff 0 /
        (coalescedPair (m + 1)).2.coeff 1 :=
      div_pos (hd.1 0 (by omega)) (hd.1 1 (by omega))
    simpa [coalescedPrevRatio, coalescedYPrev] using hpos
  · have hipos : 0 < i := by omega
    rw [coalescedPrevRatio_eq_coeff m i hipos (by omega),
      coalescedPrevRatio_eq_coeff m (i + 1) (by omega) (by omega)]
    exact coalescedJ_coeff_prev_ratio_strict (m + 1) i hipos (by omega)

end
end PhosphorylationStableCapacity
