module
public import proofs.PhosphorylationStableCapacity.SelectedBallDegreeFlowTimeTransport

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section
open PhosphorylationSharpness

/-- The small-time physical flow displacement and the scaled negative
literal field have the same conditional degree on the selected ball. -/
theorem selected_ball_degree_flow_eq_scaled_field {n : ℕ}
    (ET FT ST : ℝ) (hET : 0 < ET)
    (k : Rates n) (hk : k.Positive)
    (x : CoordinateSpace n) (r t : ℝ) (ht : 0 < t)
    (hinside : Metric.closedBall x r ⊆
      classPolytopeStrict n ET FT ST)
    (hsmall : ∀ z : classPolytope n ET FT ST,
      dist z.1 x = r →
        ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 →
          (1 - s) • (physicalForwardCurve ET FT ST hET k hk z t - z.1) +
            s • (t • restrictedFieldEuclid ET FT ST k z.1) ≠ 0)
    (D : ClosedBallDegree n x r) :
    D.degree (fun y : Metric.closedBall x r =>
      y.1 - physicalForwardCurve ET FT ST hET k hk
        (selectedBallToClass ET FT ST x r hinside y) t) =
    D.degree (fun y : Metric.closedBall x r =>
      -(t • restrictedFieldEuclid ET FT ST k y.1)) := by
  let H : ℝ → Metric.closedBall x r → CoordinateSpace n :=
    fun s y => -((1 - s) •
      (physicalForwardCurve ET FT ST hET k hk
        (selectedBallToClass ET FT ST x r hinside y) t - y.1) +
      s • (t • restrictedFieldEuclid ET FT ST k y.1))
  have hflow : Continuous (fun y : Metric.closedBall x r =>
      physicalForwardCurve ET FT ST hET k hk
        (selectedBallToClass ET FT ST x r hinside y) t) := by
    change Continuous (fun y : Metric.closedBall x r =>
      (physicalTimeMap ET FT ST hET k hk t ht.le
        (selectedBallToClass ET FT ST x r hinside y) :
          CoordinateSpace n))
    exact continuous_subtype_val.comp
      ((physicalTimeMap_continuous ET FT ST hET k hk t ht.le).comp
        (selectedBallToClass_continuous ET FT ST x r hinside))
  have hcont : ContinuousOn
      (fun p : ℝ × Metric.closedBall x r => H p.1 p.2)
      (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ) := by
    have hcoord : Continuous (fun p : ℝ × Metric.closedBall x r => p.2.1) :=
      continuous_subtype_val.comp continuous_snd
    have hcurve : Continuous (fun p : ℝ × Metric.closedBall x r =>
        physicalForwardCurve ET FT ST hET k hk
          (selectedBallToClass ET FT ST x r hinside p.2) t) :=
      hflow.comp continuous_snd
    have hfield : Continuous (fun p : ℝ × Metric.closedBall x r =>
        restrictedFieldEuclid ET FT ST k p.2.1) :=
      (differentiable_restrictedFieldEuclid ET FT ST k).continuous.comp
        hcoord
    have h : Continuous (fun p : ℝ × Metric.closedBall x r =>
        -((1 - p.1) •
          (physicalForwardCurve ET FT ST hET k hk
            (selectedBallToClass ET FT ST x r hinside p.2) t - p.2.1) +
          p.1 • (t • restrictedFieldEuclid ET FT ST k p.2.1))) :=
      by
        have hweight : Continuous (fun p : ℝ × Metric.closedBall x r =>
            (1 : ℝ) - p.1) := continuous_const.sub continuous_fst
        have htime : Continuous (fun p : ℝ × Metric.closedBall x r =>
            p.1) := continuous_fst
        have hscale : Continuous (fun _ : ℝ × Metric.closedBall x r =>
            t) := continuous_const
        apply (((hweight.smul (hcurve.sub hcoord)).add
          (htime.smul (hscale.smul hfield))).neg).congr
        intro p
        simp
    exact h.continuousOn
  have hnonzero : ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 →
      ∀ y : Metric.closedBall x r,
        dist y.1 x = r → H s y ≠ 0 := by
    intro s hs y hy
    exact neg_ne_zero.mpr
      (hsmall (selectedBallToClass ET FT ST x r hinside y) hy s hs)
  have hdeg := D.homotopy_invariant H hcont hnonzero
  have h0 : H 0 = fun y : Metric.closedBall x r =>
      y.1 - physicalForwardCurve ET FT ST hET k hk
        (selectedBallToClass ET FT ST x r hinside y) t := by
    funext y
    simp only [H, sub_zero, one_smul, zero_smul, add_zero, neg_sub]
  have h1 : H 1 = fun y : Metric.closedBall x r =>
      -(t • restrictedFieldEuclid ET FT ST k y.1) := by
    funext y
    simp only [H, sub_self, zero_smul, one_smul, zero_add]
  simpa only [h0, h1] using hdeg

end
end PhosphorylationStableCapacity
