module
public import proofs.PhosphorylationStableCapacity.ClassSmallTimeBoundaryHomotopy
public import proofs.PhosphorylationStableCapacity.FiniteDisjointAttractorBalls

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section
open PhosphorylationSharpness

/-- Any prescribed compact zero-free sphere has a uniform positive
field norm gap. The radius need not be the one chosen by the isolation
lemma. -/
theorem zero_free_sphere_has_norm_gap {n : ℕ}
    (f : CoordinateSpace n → CoordinateSpace n) (hf : Continuous f)
    (x : CoordinateSpace n) (r : ℝ)
    (hno : ∀ y : CoordinateSpace n, dist y x = r → f y ≠ 0) :
    ∃ ε : ℝ, 0 < ε ∧
      ∀ y : CoordinateSpace n, dist y x = r → ε ≤ ‖f y‖ := by
  by_cases hnon : (Metric.sphere x r).Nonempty
  · obtain ⟨y, hy, hmin⟩ :=
      (isCompact_sphere x r).exists_isMinOn hnon hf.norm.continuousOn
    refine ⟨‖f y‖, norm_pos_iff.mpr (hno y (Metric.mem_sphere.mp hy)), ?_⟩
    intro z hz
    exact hmin (Metric.mem_sphere.mpr hz)
  · refine ⟨1, by norm_num, ?_⟩
    intro z hz
    exact (hnon ⟨z, Metric.mem_sphere.mpr hz⟩).elim

/-- The zero-free rate homotopy on a selected sphere supplies the
small-time flow/field boundary homotopy on that very same sphere. -/
theorem selected_sphere_small_time_flow_field_homotopy {n : ℕ}
    (ET FT ST : ℝ) (hET : 0 < ET)
    (k k' : Rates n) (hk : k.Positive)
    (x : CoordinateSpace n) (r : ℝ)
    (hboundary : ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 →
      ∀ y : CoordinateSpace n, dist y x = r →
        restrictedFieldEuclid ET FT ST
          (ratesFromVector
            (rateVector k + t • (rateVector k' - rateVector k))) y ≠ 0) :
    ∃ ε τ : ℝ, 0 < ε ∧ 0 < τ ∧
      (∀ y : CoordinateSpace n, dist y x = r →
        ε ≤ ‖restrictedFieldEuclid ET FT ST k y‖) ∧
      ∀ z : classPolytope n ET FT ST,
        dist z.1 x = r →
        ∀ t : ℝ, 0 < t → t < τ →
          ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 →
            (1 - s) • (physicalForwardCurve ET FT ST hET k hk z t - z.1) +
              s • (t • restrictedFieldEuclid ET FT ST k z.1) ≠ 0 := by
  have hno : ∀ y : CoordinateSpace n, dist y x = r →
      restrictedFieldEuclid ET FT ST k y ≠ 0 := by
    intro y hy
    have h := hboundary 0 (by norm_num) y hy
    simpa only [zero_smul, add_zero, ratesFromVector_rateVector] using h
  obtain ⟨ε, hε, hgap⟩ := zero_free_sphere_has_norm_gap
    (restrictedFieldEuclid ET FT ST k)
    (differentiable_restrictedFieldEuclid ET FT ST k).continuous
    x r hno
  obtain ⟨τ, hτ, hsmall⟩ :=
    physical_flow_small_time_boundary_homotopy
      ET FT ST hET k hk x r ε hε hgap
  exact ⟨ε, τ, hε, hτ, hgap, hsmall⟩

end
end PhosphorylationStableCapacity
