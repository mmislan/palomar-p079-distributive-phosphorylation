module
public import proofs.PhosphorylationStableCapacity.SelectedBallDegreeRateTransport

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section
open PhosphorylationSharpness

/-- Under a genuine closed-ball degree, the no-return property makes
the identity-minus-flow degree independent of the chosen positive
time on the selected ball. -/
theorem selected_ball_degree_eq_of_positive_flow_times {n : ℕ}
    (ET FT ST : ℝ) (hET : 0 < ET)
    (k : Rates n) (hk : k.Positive)
    (x : CoordinateSpace n) (r t T : ℝ)
    (ht : 0 < t) (hT : 0 < T)
    (hinside : Metric.closedBall x r ⊆
      classPolytopeStrict n ET FT ST)
    (hnoReturn : ∀ z : classPolytope n ET FT ST,
      dist z.1 x = r → ∀ u : ℝ, 0 < u →
        physicalForwardCurve ET FT ST hET k hk z u ≠ z.1)
    (D : ClosedBallDegree n x r) :
    D.degree (fun y : Metric.closedBall x r =>
      y.1 - physicalForwardCurve ET FT ST hET k hk
        (selectedBallToClass ET FT ST x r hinside y) T) =
    D.degree (fun y : Metric.closedBall x r =>
      y.1 - physicalForwardCurve ET FT ST hET k hk
        (selectedBallToClass ET FT ST x r hinside y) t) := by
  let H : ℝ → Metric.closedBall x r → CoordinateSpace n :=
    fun s y => y.1 - physicalForwardCurve ET FT ST hET k hk
      (selectedBallToClass ET FT ST x r hinside y)
      ((1 - s) * T + s * t)
  have htime : ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 →
      0 < (1 - s) * T + s * t := by
    intro s hs
    rcases le_total T t with hle | hle
    · have hnonneg : 0 ≤ s * (t - T) :=
        mul_nonneg hs.1 (sub_nonneg.mpr hle)
      nlinarith
    · have hnonneg : 0 ≤ (1 - s) * (T - t) :=
        mul_nonneg (sub_nonneg.mpr hs.2) (sub_nonneg.mpr hle)
      nlinarith
  have hcont : ContinuousOn
      (fun p : ℝ × Metric.closedBall x r => H p.1 p.2)
      (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ) := by
    have hmap : Continuous (fun p : ℝ × Metric.closedBall x r =>
        ((1 - p.1) * T + p.1 * t, p.2)) := by
      fun_prop
    have hmaps : Set.MapsTo
        (fun p : ℝ × Metric.closedBall x r =>
          ((1 - p.1) * T + p.1 * t, p.2))
        (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ)
        (Set.Ici (0 : ℝ) ×ˢ Set.univ) := by
      intro p hp
      exact ⟨(htime p.1 hp.1).le, Set.mem_univ _⟩
    have hflow :=
      (selectedBallForwardCurve_joint_continuousOn ET FT ST hET k hk
        x r hinside).comp hmap.continuousOn hmaps
    exact (continuous_subtype_val.comp continuous_snd).continuousOn.sub hflow
  have hnonzero : ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 →
      ∀ y : Metric.closedBall x r,
        dist y.1 x = r → H s y ≠ 0 := by
    intro s hs y hy
    exact sub_ne_zero.mpr
      (hnoReturn (selectedBallToClass ET FT ST x r hinside y)
        hy _ (htime s hs)).symm
  have hdeg := D.homotopy_invariant H hcont hnonzero
  have h0 : H 0 = fun y : Metric.closedBall x r =>
      y.1 - physicalForwardCurve ET FT ST hET k hk
        (selectedBallToClass ET FT ST x r hinside y) T := by
    funext y
    simp only [H, sub_zero, one_mul, zero_mul, add_zero]
  have h1 : H 1 = fun y : Metric.closedBall x r =>
      y.1 - physicalForwardCurve ET FT ST hET k hk
        (selectedBallToClass ET FT ST x r hinside y) t := by
    funext y
    simp only [H, sub_self, zero_mul, one_mul, zero_add]
  simpa only [h0, h1] using hdeg

end
end PhosphorylationStableCapacity
