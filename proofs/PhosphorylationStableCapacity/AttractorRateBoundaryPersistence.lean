module
public import proofs.PhosphorylationStableCapacity.AttractorBoundaryGap
public import proofs.PhosphorylationStableCapacity.CompactParameterUniformity
public import proofs.PhosphorylationStableCapacity.SplitJacobianContinuity
public import Mathlib.Analysis.Normed.Module.Convex
public import proofs.PhosphorylationStableCapacity.AttractorBoundaryGapSmall

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section

open PhosphorylationSharpness

/-- The enclosing sphere of any literal local attractor remains zero-free
under sufficiently small changes to all six arrays of rate constants.
This includes nonhyperbolic attractors. -/
theorem local_attractor_boundary_zero_free_near_rates {n : ℕ}
    (ET FT ST : ℝ) (k : Rates n) (x : CoordinateSpace n)
    (hx : IsLocallyAsymptoticallyStableClass ET FT ST k x) :
    ∃ r δ : ℝ, 0 < r ∧ 0 < δ ∧
      ∀ v : RateVector n, dist v (rateVector k) < δ →
        ∀ y : CoordinateSpace n, dist y x = r →
          restrictedFieldEuclid ET FT ST (ratesFromVector v) y ≠ 0 := by
  obtain ⟨r, ε, hr, hε, hgap⟩ :=
    local_attractor_exists_boundary_gap ET FT ST k x hx
  have hcont : Continuous
      (fun z : RateVector n × CoordinateSpace n =>
        restrictedFieldEuclid ET FT ST (ratesFromVector z.1) z.2) :=
    (contDiff_jointRestrictedField ET FT ST).continuous
  obtain ⟨δ, hδ, hnear⟩ :=
    continuous_family_uniform_near_compact
      (fun v y => restrictedFieldEuclid ET FT ST (ratesFromVector v) y)
      hcont (rateVector k) (Metric.sphere x r)
      (isCompact_sphere x r) (ε / 2) (by linarith)
  refine ⟨r, δ, hr, hδ, ?_⟩
  intro v hv y hy hzero
  have hsmall := hnear v hv y (Metric.mem_sphere.mpr hy)
  rw [ratesFromVector_rateVector, hzero, zero_sub, norm_neg] at hsmall
  have hlarge := hgap y hy
  linarith

/-- The literal field stays zero-free on the same sphere throughout the
straight rate homotopy from an attracting parameter to a nearby one. -/
theorem local_attractor_boundary_zero_free_rate_homotopy {n : ℕ}
    (ET FT ST : ℝ) (k : Rates n) (x : CoordinateSpace n)
    (hx : IsLocallyAsymptoticallyStableClass ET FT ST k x) :
    ∃ r δ : ℝ, 0 < r ∧ 0 < δ ∧
      ∀ v : RateVector n, dist v (rateVector k) < δ →
        ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 →
          ∀ y : CoordinateSpace n, dist y x = r →
            restrictedFieldEuclid ET FT ST
              (ratesFromVector
                (rateVector k + t • (v - rateVector k))) y ≠ 0 := by
  obtain ⟨r, δ, hr, hδ, hboundary⟩ :=
    local_attractor_boundary_zero_free_near_rates ET FT ST k x hx
  refine ⟨r, δ, hr, hδ, ?_⟩
  intro v hv t ht y hy
  apply hboundary _ ?_ y hy
  have hbase : rateVector k ∈ Metric.ball (rateVector k) δ :=
    Metric.mem_ball_self hδ
  have htarget : v ∈ Metric.ball (rateVector k) δ :=
    Metric.mem_ball.mpr hv
  have hpath := (convex_ball (rateVector k) δ).add_smul_sub_mem
    hbase htarget ht
  exact Metric.mem_ball.mp hpath

/-- The exact rate-line homotopy is jointly continuous in time and class
state, with no assumption that either endpoint equilibrium is regular. -/
theorem continuous_restricted_field_rate_homotopy {n : ℕ}
    (ET FT ST : ℝ) (k : Rates n) (v : RateVector n) :
    Continuous (fun z : ℝ × CoordinateSpace n =>
      restrictedFieldEuclid ET FT ST
        (ratesFromVector
          (rateVector k + z.1 • (v - rateVector k))) z.2) := by
  have hmap : Continuous (fun z : ℝ × CoordinateSpace n =>
      (rateVector k + z.1 • (v - rateVector k), z.2)) := by
    fun_prop
  have hjoint : Continuous (jointRestrictedField (n := n) ET FT ST) :=
    (contDiff_jointRestrictedField ET FT ST).continuous
  simpa only [jointRestrictedField, Function.comp_def] using hjoint.comp hmap

/-- A prescribed enclosing sphere with a positive field margin stays
zero-free during every sufficiently short literal rate homotopy. -/
theorem boundary_zero_free_rate_homotopy_of_gap {n : ℕ}
    (ET FT ST : ℝ) (k : Rates n) (x : CoordinateSpace n)
    (r ε : ℝ) (hε : 0 < ε)
    (hgap : ∀ y : CoordinateSpace n, dist y x = r →
      ε ≤ ‖restrictedFieldEuclid ET FT ST k y‖) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ v : RateVector n, dist v (rateVector k) < δ →
        ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 →
          ∀ y : CoordinateSpace n, dist y x = r →
            restrictedFieldEuclid ET FT ST
              (ratesFromVector
                (rateVector k + t • (v - rateVector k))) y ≠ 0 := by
  have hcont : Continuous
      (fun z : RateVector n × CoordinateSpace n =>
        restrictedFieldEuclid ET FT ST (ratesFromVector z.1) z.2) :=
    (contDiff_jointRestrictedField ET FT ST).continuous
  obtain ⟨δ, hδ, hnear⟩ :=
    continuous_family_uniform_near_compact
      (fun v y => restrictedFieldEuclid ET FT ST (ratesFromVector v) y)
      hcont (rateVector k) (Metric.sphere x r)
      (isCompact_sphere x r) (ε / 2) (by linarith)
  refine ⟨δ, hδ, ?_⟩
  intro v hv t ht y hy hzero
  have hbase : rateVector k ∈ Metric.ball (rateVector k) δ :=
    Metric.mem_ball_self hδ
  have htarget : v ∈ Metric.ball (rateVector k) δ :=
    Metric.mem_ball.mpr hv
  have hpath := (convex_ball (rateVector k) δ).add_smul_sub_mem
    hbase htarget ht
  have hsmall := hnear _ (Metric.mem_ball.mp hpath) y
    (Metric.mem_sphere.mpr hy)
  rw [ratesFromVector_rateVector, hzero, zero_sub, norm_neg] at hsmall
  have hlarge := hgap y hy
  linarith

/-- The rate homotopy sphere can be chosen smaller than any requested
positive radius, so finitely many distinct attractors may receive
separate neighborhoods before a common regular perturbation. -/
theorem local_attractor_boundary_zero_free_rate_homotopy_below {n : ℕ}
    (ET FT ST : ℝ) (k : Rates n) (x : CoordinateSpace n)
    (hx : IsLocallyAsymptoticallyStableClass ET FT ST k x)
    (R : ℝ) (hR : 0 < R) :
    ∃ r δ : ℝ, 0 < r ∧ r < R ∧ 0 < δ ∧
      ∀ v : RateVector n, dist v (rateVector k) < δ →
        ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 →
          ∀ y : CoordinateSpace n, dist y x = r →
            restrictedFieldEuclid ET FT ST
              (ratesFromVector
                (rateVector k + t • (v - rateVector k))) y ≠ 0 := by
  obtain ⟨r, ε, hr, hrR, hε, hgap⟩ :=
    local_attractor_exists_boundary_gap_below ET FT ST k x hx R hR
  obtain ⟨δ, hδ, hboundary⟩ :=
    boundary_zero_free_rate_homotopy_of_gap ET FT ST k x r ε hε hgap
  exact ⟨r, δ, hr, hrR, hδ, hboundary⟩

end
end PhosphorylationStableCapacity
