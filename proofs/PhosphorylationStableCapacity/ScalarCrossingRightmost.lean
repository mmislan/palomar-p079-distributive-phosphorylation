module
public import proofs.PhosphorylationStableCapacity.ScalarCrossingLast

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section

/-- The rightmost simple interior root has the orientation determined
by the sign at the right endpoint, regardless of the left endpoint. -/
theorem rightmost_simple_root_orientation
    (f : ℝ → ℝ) (a b : ℝ)
    (hcont : ContinuousOn f (Set.Icc a b))
    (hb : f b ≠ 0)
    (hfinite : {r : ℝ | a < r ∧ r < b ∧ f r = 0}.Finite)
    (hnonempty : ∃ r, a < r ∧ r < b ∧ f r = 0)
    (hsimple : ∀ r, a < r → r < b → f r = 0 →
      deriv f r ≠ 0) :
    ∃ r, a < r ∧ r < b ∧ f r = 0 ∧
      (∀ z, a < z → z < b → f z = 0 → z ≤ r) ∧
      (0 < deriv f r ↔ 0 < f b) := by
  let R : Set ℝ := {r | a < r ∧ r < b ∧ f r = 0}
  let S : Finset ℝ := hfinite.toFinset
  obtain ⟨r₀, hr₀a, hr₀b, hr₀f⟩ := hnonempty
  have hSne : S.Nonempty := by
    refine ⟨r₀, ?_⟩
    exact hfinite.mem_toFinset.mpr ⟨hr₀a, hr₀b, hr₀f⟩
  let r := S.max' hSne
  have hrmem : r ∈ R :=
    hfinite.mem_toFinset.mp (Finset.max'_mem S hSne)
  have hrmax : ∀ z ∈ R, z ≤ r := by
    intro z hz
    exact Finset.le_max' S z (hfinite.mem_toFinset.mpr hz)
  obtain ⟨hra, hrb, hrf⟩ := hrmem
  have hdne := hsimple r hra hrb hrf
  have hsign : 0 < deriv f r ↔ 0 < f b := by
    rcases lt_or_gt_of_ne hb with hbneg | hbpos
    · have hdneg : deriv f r < 0 := by
        rcases lt_or_gt_of_ne hdne with hdneg | hdpos
        · exact hdneg
        · obtain ⟨_l, h, _hal, _hlr, hrh, hhb, hcase⟩ :=
            simple_root_local_crossing f a r b hra hrb hrf hdne
          have hfh : 0 < f h := by
            simp [hdpos] at hcase
            exact hcase.2
          have hcont' : ContinuousOn f (Set.Icc h b) := by
            apply hcont.mono
            intro x hx
            exact ⟨le_trans (le_of_lt (lt_trans hra hrh)) hx.1, hx.2⟩
          obtain ⟨z, hhz, hzb, hfz⟩ :=
            scalar_root_between_pos_neg f h b hhb.le hcont' hfh hbneg
          have haz : a < z := lt_trans (lt_trans hra hrh) hhz
          have hzle : z ≤ r := hrmax z ⟨haz, hzb, hfz⟩
          linarith
      exact ⟨fun h => (not_lt_of_ge hdneg.le h).elim,
        fun h => (not_lt_of_ge hbneg.le h).elim⟩
    · have hdpos : 0 < deriv f r := by
        rcases lt_or_gt_of_ne hdne with hdneg | hdpos
        · obtain ⟨_l, h, _hal, _hlr, hrh, hhb, hcase⟩ :=
            simple_root_local_crossing f a r b hra hrb hrf hdne
          have hfh : f h < 0 := by
            simp [not_lt.mpr hdneg.le] at hcase
            exact hcase.2
          have hcont' : ContinuousOn f (Set.Icc h b) := by
            apply hcont.mono
            intro x hx
            exact ⟨le_trans (le_of_lt (lt_trans hra hrh)) hx.1, hx.2⟩
          obtain ⟨z, hhz, hzb, hfz⟩ :=
            scalar_root_between_neg_pos f h b hhb.le hcont' hfh hbpos
          have haz : a < z := lt_trans (lt_trans hra hrh) hhz
          have hzle : z ≤ r := hrmax z ⟨haz, hzb, hfz⟩
          linarith
        · exact hdpos
      exact ⟨fun _ => hbpos, fun _ => hdpos⟩
  exact ⟨r, hra, hrb, hrf,
    fun z hza hzb hfz => hrmax z ⟨hza, hzb, hfz⟩,
    hsign⟩

end
end PhosphorylationStableCapacity
