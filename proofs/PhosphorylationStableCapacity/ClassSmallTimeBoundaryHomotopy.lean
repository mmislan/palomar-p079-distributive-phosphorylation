module
public import proofs.PhosphorylationStableCapacity.ClassAttractorIndexAnalyticData

@[expose] public section

namespace PhosphorylationStableCapacity

open PhosphorylationSharpness

noncomputable section

/-- On any sphere with a positive field norm margin, the uniform
quadratic time-flow error makes the field and the small-time
displacement connected by a zero-free straight-line homotopy. -/
theorem physical_flow_small_time_boundary_homotopy {n : ℕ}
    (ET FT ST : ℝ) (hET : 0 < ET)
    (k : Rates n) (hk : k.Positive)
    (x : CoordinateSpace n) (r ε : ℝ)
    (hε : 0 < ε)
    (hgap : ∀ y : CoordinateSpace n, dist y x = r →
      ε ≤ ‖restrictedFieldEuclid ET FT ST k y‖) :
    ∃ τ : ℝ, 0 < τ ∧
      ∀ (z : classPolytope n ET FT ST),
        dist z.1 x = r →
        ∀ t : ℝ, 0 < t → t < τ →
          ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 →
            (1 - s) • (physicalForwardCurve ET FT ST hET k hk z t - z.1) +
              s • (t • restrictedFieldEuclid ET FT ST k z.1) ≠ 0 := by
  obtain ⟨D, hD, herror⟩ :=
    exists_physical_flow_quadratic_time_error ET FT ST hET k hk
  let τ := ε / (D + 1)
  have hden : 0 < D + 1 := by linarith
  have hτ : 0 < τ := div_pos hε hden
  refine ⟨τ, hτ, ?_⟩
  intro z hz t ht htτ s hs
  let v := physicalForwardCurve ET FT ST hET k hk z t - z.1
  let w := t • restrictedFieldEuclid ET FT ST k z.1
  have hDsmall : D * t < ε := by
    have h := (lt_div_iff₀ hden).mp htτ
    nlinarith
  have herrorlt : D * t * t < ε * t := by
    have h := mul_lt_mul_of_pos_right hDsmall ht
    nlinarith
  have hwlower : ε * t ≤ ‖w‖ := by
    have hg := hgap z.1 hz
    have hmul := mul_le_mul_of_nonneg_left hg ht.le
    simpa [w, norm_smul, Real.norm_eq_abs, abs_of_pos ht, mul_comm] using hmul
  have hwpos : 0 < ‖w‖ := lt_of_lt_of_le (mul_pos hε ht) hwlower
  have hvball : v ∈ Metric.ball w ‖w‖ := by
    rw [Metric.mem_ball, dist_eq_norm]
    have he := herror z t ht.le
    exact lt_of_le_of_lt he (herrorlt.trans_le hwlower)
  have hwball : w ∈ Metric.ball w ‖w‖ := Metric.mem_ball_self hwpos
  have hcombo := (convex_iff_add_mem).mp (convex_ball w ‖w‖)
    hvball hwball (sub_nonneg.mpr hs.2) hs.1 (by ring)
  intro hzero
  change (1 - s) • v + s • w = 0 at hzero
  have hbad := Metric.mem_ball.mp hcombo
  rw [hzero, dist_zero_left] at hbad
  exact (lt_irrefl _ hbad).elim

/-- All analytic boundary inputs for an attracting local index, with
no regularity assumption on its Jacobian. A degree/index theorem is
still needed to convert these inputs into a signed local count. -/
theorem local_attractor_degree_bridge_data {n : ℕ}
    (ET FT ST : ℝ) (hET : 0 < ET)
    (k : Rates n) (hk : k.Positive)
    (x : CoordinateSpace n)
    (hx : IsLocallyAsymptoticallyStableClass ET FT ST k x)
    (hxmem : x ∈ classPolytope n ET FT ST) :
    ∃ r ε τ T : ℝ, 0 < r ∧ 0 < ε ∧ 0 < τ ∧ 0 < T ∧
      (∀ y : CoordinateSpace n, dist y x = r →
        ε ≤ ‖restrictedFieldEuclid ET FT ST k y‖) ∧
      (∀ z ∈ Metric.closedBall (⟨x, hxmem⟩ :
          classPolytope n ET FT ST) r,
        dist (physicalForwardCurve ET FT ST hET k hk z T) x < r) ∧
      (∀ z : classPolytope n ET FT ST,
        dist z.1 x = r →
          ∀ t : ℝ, 0 < t →
            physicalForwardCurve ET FT ST hET k hk z t ≠ z.1) ∧
      (∀ z : classPolytope n ET FT ST,
        dist z.1 x = r →
          ∀ t : ℝ, 0 < t → t < τ →
            ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 →
              (1 - s) • (physicalForwardCurve ET FT ST hET k hk z t - z.1) +
                s • (t • restrictedFieldEuclid ET FT ST k z.1) ≠ 0) := by
  obtain ⟨r, ε, hr, hε, T, hT, hinward, hnoreturn, hgap⟩ :=
    local_attractor_index_analytic_data ET FT ST hET k hk x hx hxmem
  obtain ⟨τ, hτ, hsmall⟩ :=
    physical_flow_small_time_boundary_homotopy
      ET FT ST hET k hk x r ε hε hgap
  refine ⟨r, ε, τ, T, hr, hε, hτ, hT, hgap,
    hinward, ?_, hsmall⟩
  intro z hz
  have hz' : dist z (⟨x, hxmem⟩ : classPolytope n ET FT ST) = r := by
    simpa only [Subtype.dist_eq] using hz
  exact hnoreturn z hz'

end
end PhosphorylationStableCapacity
