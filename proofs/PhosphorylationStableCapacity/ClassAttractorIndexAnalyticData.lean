module
public import proofs.PhosphorylationStableCapacity.ClassNoPeriodicInBasin
public import proofs.PhosphorylationStableCapacity.AttractorBoundaryGapSmall

@[expose] public section

namespace PhosphorylationStableCapacity

open PhosphorylationSharpness

noncomputable section

/-- Analytic data for the local fixed-point index of an arbitrary
literal attractor, including a nonhyperbolic one: one ball has a
strictly inward positive-time map and no positive-time fixed points
on its boundary. -/
theorem local_attractor_index_analytic_data {n : ℕ}
    (ET FT ST : ℝ) (hET : 0 < ET)
    (k : Rates n) (hk : k.Positive)
    (x : CoordinateSpace n)
    (hx : IsLocallyAsymptoticallyStableClass ET FT ST k x)
    (hxmem : x ∈ classPolytope n ET FT ST) :
    ∃ r ε : ℝ, 0 < r ∧ 0 < ε ∧ ∃ T : ℝ, 0 < T ∧
      (∀ z ∈ Metric.closedBall (⟨x, hxmem⟩ :
          classPolytope n ET FT ST) r,
        dist (physicalForwardCurve ET FT ST hET k hk z T) x < r) ∧
      (∀ z : classPolytope n ET FT ST,
        dist z (⟨x, hxmem⟩ : classPolytope n ET FT ST) = r →
          ∀ t : ℝ, 0 < t →
            physicalForwardCurve ET FT ST hET k hk z t ≠ z.1) ∧
      (∀ y : CoordinateSpace n, dist y x = r →
        ε ≤ ‖restrictedFieldEuclid ET FT ST k y‖) := by
  obtain ⟨r₀, hr₀, huniform⟩ :=
    local_attractor_uniform_on_closedBall ET FT ST hET k hk x hx hxmem
  obtain ⟨δ, hδ, hnoreturn⟩ :=
    local_attractor_no_positive_time_return ET FT ST hET k hk x hx
  have hR : 0 < min r₀ δ := lt_min hr₀ hδ
  obtain ⟨r, ε, hr, hrR, hε, hgap⟩ :=
    local_attractor_exists_boundary_gap_below
      ET FT ST k x hx (min r₀ δ) hR
  have hrle : r ≤ r₀ := (le_of_lt hrR).trans (min_le_left _ _)
  have hrδ : r < δ := hrR.trans_le (min_le_right _ _)
  obtain ⟨T₀, hT₀, hinward₀⟩ := huniform r hr
  let T := max 1 T₀
  have hT : 0 < T := by dsimp [T]; exact lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  have hT₀T : T₀ ≤ T := le_max_right _ _
  refine ⟨r, ε, hr, hε, T, hT, ?_, ?_, hgap⟩
  · intro z hz
    have hz₀ : z ∈ Metric.closedBall
        (⟨x, hxmem⟩ : classPolytope n ET FT ST) r₀ := by
      exact Metric.mem_closedBall.mpr ((Metric.mem_closedBall.mp hz).trans hrle)
    exact hinward₀ z hz₀ T hT₀T
  · intro z hz t ht hfixed
    have hz' : dist z.1 x < δ := by
      have heq : dist z.1 x = r := by simpa only [Subtype.dist_eq] using hz
      linarith
    have hzx := hnoreturn z hz' t ht hfixed
    have heq : dist z.1 x = r := by simpa only [Subtype.dist_eq] using hz
    have hzero : dist z.1 x = 0 := by simp [hzx]
    linarith

end
end PhosphorylationStableCapacity
