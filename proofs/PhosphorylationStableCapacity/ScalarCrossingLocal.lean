module
public import Mathlib.Analysis.Calculus.DerivativeTest

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section
open Filter
open scoped Topology

/-- A simple increasing root has a negative value arbitrarily close
on its left, within any prescribed left interval. -/
theorem exists_negative_left_of_deriv_pos
    (f : ℝ → ℝ) (a r : ℝ) (ha : a < r)
    (hr : f r = 0) (hd : 0 < deriv f r) :
    ∃ x, a < x ∧ x < r ∧ f x < 0 := by
  have hsign := eventually_nhdsWithin_sign_eq_of_deriv_pos hd hr
  have hleft : ∀ᶠ x in 𝓝[<] r, f x < 0 := by
    filter_upwards [nhdsWithin_le_nhds hsign, self_mem_nhdsWithin]
      with x hxsign hxlt
    rw [sign_neg (sub_neg.mpr hxlt)] at hxsign
    exact sign_eq_neg_one_iff.mp hxsign
  have habove : ∀ᶠ x in 𝓝[<] r, a < x :=
    nhdsWithin_le_nhds (isOpen_Ioi.mem_nhds ha)
  obtain ⟨x, hfx, hax, hxr⟩ :=
    (hleft.and (habove.and self_mem_nhdsWithin)).exists
  exact ⟨x, hax, hxr, hfx⟩

/-- A simple increasing root has a positive value arbitrarily close
on its right, within any prescribed right interval. -/
theorem exists_positive_right_of_deriv_pos
    (f : ℝ → ℝ) (r b : ℝ) (hb : r < b)
    (hr : f r = 0) (hd : 0 < deriv f r) :
    ∃ x, r < x ∧ x < b ∧ 0 < f x := by
  have hsign := eventually_nhdsWithin_sign_eq_of_deriv_pos hd hr
  have hright : ∀ᶠ x in 𝓝[>] r, 0 < f x := by
    filter_upwards [nhdsWithin_le_nhds hsign, self_mem_nhdsWithin]
      with x hxsign hxr
    rw [sign_pos (sub_pos.mpr hxr)] at hxsign
    exact sign_eq_one_iff.mp hxsign
  have hbelow : ∀ᶠ x in 𝓝[>] r, x < b :=
    nhdsWithin_le_nhds (isOpen_Iio.mem_nhds hb)
  obtain ⟨x, hfx, hxb, hrx⟩ :=
    (hright.and (hbelow.and self_mem_nhdsWithin)).exists
  exact ⟨x, hrx, hxb, hfx⟩

/-- Local sign witnesses for either orientation of a simple root. -/
theorem simple_root_local_crossing
    (f : ℝ → ℝ) (a r b : ℝ) (ha : a < r) (hb : r < b)
    (hr : f r = 0) (hd : deriv f r ≠ 0) :
    ∃ l h, a < l ∧ l < r ∧ r < h ∧ h < b ∧
      (if 0 < deriv f r then f l < 0 ∧ 0 < f h
       else 0 < f l ∧ f h < 0) := by
  rcases lt_or_gt_of_ne hd with hneg | hpos
  · have hp : 0 < deriv (-f) r := by simpa [deriv.neg] using neg_pos.mpr hneg
    have hz : (-f) r = 0 := by simp [hr]
    obtain ⟨l, hal, hlr, hlf⟩ :=
      exists_negative_left_of_deriv_pos (-f) a r ha hz hp
    obtain ⟨h, hrh, hhb, hhf⟩ :=
      exists_positive_right_of_deriv_pos (-f) r b hb hz hp
    refine ⟨l, h, hal, hlr, hrh, hhb, ?_⟩
    simp [hneg.not_gt]
    change -(f l) < 0 at hlf
    change 0 < -(f h) at hhf
    constructor <;> linarith
  · obtain ⟨l, hal, hlr, hlf⟩ :=
      exists_negative_left_of_deriv_pos f a r ha hr hpos
    obtain ⟨h, hrh, hhb, hhf⟩ :=
      exists_positive_right_of_deriv_pos f r b hb hr hpos
    exact ⟨l, h, hal, hlr, hrh, hhb, by simp [hpos, hlf, hhf]⟩

end
end PhosphorylationStableCapacity
