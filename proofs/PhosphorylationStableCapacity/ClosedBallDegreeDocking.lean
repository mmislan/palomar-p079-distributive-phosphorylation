module
public import proofs.PhosphorylationStableCapacity.SelectedBallDegreePositiveScale
public import proofs.PhosphorylationStableCapacity.UniversalCeilingLocalIndexDocking

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section
attribute [local instance] Classical.propDecidable
open PhosphorylationSharpness

/-- The one remaining uniform topological existence premise: a degree
on each positive-radius finite-dimensional closed ball satisfying the
explicit homotopy, normalization and regular-zero fields in
`ClosedBallDegree`. No such degree is constructed by this definition. -/
def ClosedBallDegreeExists : Prop :=
  ∀ (n : ℕ) (x : CoordinateSpace n) (r : ℝ),
    0 < r → Nonempty (ClosedBallDegree n x r)

/-- All P079-specific analytic, orientation, finite-zero and sum
transport now reduce the local attractor index to the genuine
closed-ball degree construction. -/
theorem localAttractorIndexPrinciple_of_closedBallDegree
    (hdegree : ClosedBallDegreeExists) :
    LocalAttractorIndexPrinciple := by
  intro n hn ET FT ST hET hFT hST k k' hk hk'
    xs hxs r hr hinside hinward hnoReturn
    E hE hfinite hregular hboundary i
  let x := xs i
  let ri := r i
  obtain ⟨D⟩ := hdegree n x ri (hr i)
  obtain ⟨T, hT, hTinward⟩ := hinward i
  have hTdeg := selectedBallTimeMap_degree_one
    ET FT ST hET k hk x ri T (hr i) hT.le
    (hinside i) hTinward D
  obtain ⟨ε, τ, hε, hτ, hgap, hsmall⟩ :=
    selected_sphere_small_time_flow_field_homotopy
      ET FT ST hET k k' hk x ri (hboundary i)
  let t : ℝ := τ / 2
  have ht : 0 < t := by dsimp [t]; linarith
  have htτ : t < τ := by dsimp [t]; linarith
  have htime := selected_ball_degree_eq_of_positive_flow_times
    ET FT ST hET k hk x ri t T ht hT (hinside i)
    (hnoReturn i) D
  have hflowField := selected_ball_degree_flow_eq_scaled_field
    ET FT ST hET k hk x ri t ht (hinside i)
    (by
      intro z hz s hs
      exact hsmall z hz t ht htτ s hs) D
  have hscale := closed_ball_degree_positive_scale
    x ri t ht (restrictedFieldEuclid ET FT ST k)
    (differentiable_restrictedFieldEuclid ET FT ST k).continuous
    (by
      intro y hy
      have h := hboundary i 0 (by norm_num) y hy
      simpa only [zero_smul, add_zero,
        ratesFromVector_rateVector] using h) D
  have hrate := selected_ball_degree_eq_of_rate_homotopy
    ET FT ST k k' x ri D (hboundary i)
  have hnewBoundary : ∀ y : CoordinateSpace n,
      dist y x = ri →
        restrictedFieldEuclid ET FT ST k' y ≠ 0 := by
    intro y hy
    have h := hboundary i 1 (by norm_num) y hy
    have hv : rateVector k + (rateVector k' - rateVector k) =
        rateVector k' := by abel
    simpa only [one_smul, hv, ratesFromVector_rateVector] using h
  have hsum := selected_ball_signed_sum_eq_degree_of_regular
    ET FT ST k' x ri (hinside i) E hE hfinite hregular
    hnewBoundary D
  calc
    (∑ z ∈ hfinite.toFinset.filter
      (fun z => toCoordinateSpace (chart z) ∈
        Metric.closedBall (xs i) (r i)),
      signedNegativeFieldIndex ET FT ST k' z) =
        D.degree (fun y : Metric.closedBall x ri =>
          -restrictedFieldEuclid ET FT ST k' y.1) := hsum
    _ = D.degree (fun y : Metric.closedBall x ri =>
          -restrictedFieldEuclid ET FT ST k y.1) := hrate.symm
    _ = D.degree (fun y : Metric.closedBall x ri =>
          -(t • restrictedFieldEuclid ET FT ST k y.1)) := hscale.symm
    _ = D.degree (fun y : Metric.closedBall x ri =>
          y.1 - physicalForwardCurve ET FT ST hET k hk
            (selectedBallToClass ET FT ST x ri (hinside i) y) t) :=
      hflowField.symm
    _ = D.degree (fun y : Metric.closedBall x ri =>
          y.1 - physicalForwardCurve ET FT ST hET k hk
            (selectedBallToClass ET FT ST x ri (hinside i) y) T) :=
      htime.symm
    _ = 1 := by
      simpa only [selectedBallTimeMap] using hTdeg

/-- The exact P079 capacity endpoint now has one explicitly pure
topological premise: construction of the closed-ball degree interface
at every positive radius. This theorem does not prove that premise. -/
theorem all_size_exact_capacity_of_closedBallDegree
    (hdegree : ClosedBallDegreeExists)
    (n : ℕ) (hn : 1 ≤ n) :
    ExactNonlinearStableCapacity n :=
  all_size_exact_capacity_of_local_attractor_indices
    (localAttractorIndexPrinciple_of_closedBallDegree hdegree) n hn

end
end PhosphorylationStableCapacity
