module
public import proofs.PhosphorylationStableCapacity.ScalarCrossingLocal

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section

/-- Opposite strict endpoint signs force an interior zero. -/
theorem scalar_root_between_neg_pos
    (f : ℝ → ℝ) (a b : ℝ) (hab : a ≤ b)
    (hcont : ContinuousOn f (Set.Icc a b))
    (ha : f a < 0) (hb : 0 < f b) :
    ∃ r, a < r ∧ r < b ∧ f r = 0 := by
  have hzero : (0 : ℝ) ∈ Set.Icc (f a) (f b) :=
    ⟨ha.le, hb.le⟩
  obtain ⟨r, hr, hroot⟩ := (Set.mem_image _ _ _).mp
    (intermediate_value_Icc hab hcont hzero)
  have har : a < r := by
    rcases hr.1.eq_or_lt with h | h
    · rw [←h] at hroot
      linarith
    · exact h
  have hrb : r < b := by
    rcases hr.2.eq_or_lt with h | h
    · rw [h] at hroot
      linarith
    · exact h
  exact ⟨r, har, hrb, hroot⟩

theorem scalar_root_between_pos_neg
    (f : ℝ → ℝ) (a b : ℝ) (hab : a ≤ b)
    (hcont : ContinuousOn f (Set.Icc a b))
    (ha : 0 < f a) (hb : f b < 0) :
    ∃ r, a < r ∧ r < b ∧ f r = 0 := by
  have hneg : ContinuousOn (fun x => -f x) (Set.Icc a b) :=
    hcont.neg
  obtain ⟨r, har, hrb, hr⟩ := scalar_root_between_neg_pos
    (fun x => -f x) a b hab hneg (by simpa using ha)
      (by simpa using hb)
  exact ⟨r, har, hrb, by simpa using hr⟩

/-- Among finitely many simple roots, the rightmost root before a
positive endpoint is an increasing crossing when the left endpoint
is negative. -/
theorem rightmost_scalar_root_deriv_pos
    (f : ℝ → ℝ) (a b : ℝ) (hab : a < b)
    (hcont : ContinuousOn f (Set.Icc a b))
    (ha : f a < 0) (hb : 0 < f b)
    (hfinite : {r : ℝ | a < r ∧ r < b ∧ f r = 0}.Finite)
    (hsimple : ∀ r, a < r → r < b → f r = 0 →
      deriv f r ≠ 0) :
    ∃ r, a < r ∧ r < b ∧ f r = 0 ∧
      (∀ z, a < z → z < b → f z = 0 → z ≤ r) ∧
      0 < deriv f r := by
  let R : Set ℝ := {r | a < r ∧ r < b ∧ f r = 0}
  let S : Finset ℝ := hfinite.toFinset
  obtain ⟨r₀, hr₀a, hr₀b, hr₀f⟩ :=
    scalar_root_between_neg_pos f a b hab.le hcont ha hb
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
  have hdpos : 0 < deriv f r := by
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
        scalar_root_between_neg_pos f h b hhb.le hcont' hfh hb
      have haz : a < z := lt_trans (lt_trans hra hrh) hhz
      have hzle : z ≤ r := hrmax z ⟨haz, hzb, hfz⟩
      linarith
    · exact hdpos
  exact ⟨r, hra, hrb, hrf,
    fun z hza hzb hfz => hrmax z ⟨hza, hzb, hfz⟩,
    hdpos⟩

/-- The rightmost simple root before a negative endpoint is a
decreasing crossing when the left endpoint is positive. -/
theorem rightmost_scalar_root_deriv_neg
    (f : ℝ → ℝ) (a b : ℝ) (hab : a < b)
    (hcont : ContinuousOn f (Set.Icc a b))
    (ha : 0 < f a) (hb : f b < 0)
    (hfinite : {r : ℝ | a < r ∧ r < b ∧ f r = 0}.Finite)
    (hsimple : ∀ r, a < r → r < b → f r = 0 →
      deriv f r ≠ 0) :
    ∃ r, a < r ∧ r < b ∧ f r = 0 ∧
      (∀ z, a < z → z < b → f z = 0 → z ≤ r) ∧
      deriv f r < 0 := by
  have hfinite' : {r : ℝ | a < r ∧ r < b ∧ (-f) r = 0}.Finite := by
    convert hfinite using 1
    ext r
    simp
  have hsimple' : ∀ r, a < r → r < b → (-f) r = 0 →
      deriv (-f) r ≠ 0 := by
    intro r har hrb hroot
    simpa [deriv.neg] using hsimple r har hrb (by simpa using hroot)
  obtain ⟨r, har, hrb, hroot, hmax, hderiv⟩ :=
    rightmost_scalar_root_deriv_pos (-f) a b hab hcont.neg
      (by simpa using ha) (by simpa using hb)
      hfinite' hsimple'
  refine ⟨r, har, hrb, by simpa using hroot, ?_, ?_⟩
  · intro z haz hzb hz
    exact hmax z haz hzb (by simpa using hz)
  · simpa [deriv.neg] using hderiv

end
end PhosphorylationStableCapacity
