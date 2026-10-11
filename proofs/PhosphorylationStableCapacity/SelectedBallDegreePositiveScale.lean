module
public import proofs.PhosphorylationStableCapacity.SelectedBallDegreeSmallTimeTransport

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section

/-- Positive scaling of a continuous zero-free-boundary field leaves
its conditional closed-ball degree unchanged. -/
theorem closed_ball_degree_positive_scale {n : ℕ}
    (x : CoordinateSpace n) (r t : ℝ) (ht : 0 < t)
    (f : CoordinateSpace n → CoordinateSpace n) (hf : Continuous f)
    (hboundary : ∀ y : CoordinateSpace n, dist y x = r → f y ≠ 0)
    (D : ClosedBallDegree n x r) :
    D.degree (fun y : Metric.closedBall x r => -(t • f y.1)) =
    D.degree (fun y : Metric.closedBall x r => -f y.1) := by
  let H : ℝ → Metric.closedBall x r → CoordinateSpace n :=
    fun s y => -(((1 - s) * t + s) • f y.1)
  have hscale : ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 →
      0 < (1 - s) * t + s := by
    intro s hs
    rcases le_total t 1 with hle | hle
    · have hnonneg : 0 ≤ s * (1 - t) :=
        mul_nonneg hs.1 (sub_nonneg.mpr hle)
      nlinarith
    · have hnonneg : 0 ≤ (1 - s) * (t - 1) :=
        mul_nonneg (sub_nonneg.mpr hs.2) (sub_nonneg.mpr hle)
      nlinarith
  have hcont : ContinuousOn
      (fun p : ℝ × Metric.closedBall x r => H p.1 p.2)
      (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ) := by
    have h : Continuous (fun p : ℝ × Metric.closedBall x r =>
        -(((1 - p.1) * t + p.1) • f p.2.1)) := by
      fun_prop
    exact h.continuousOn
  have hnonzero : ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 →
      ∀ y : Metric.closedBall x r,
        dist y.1 x = r → H s y ≠ 0 := by
    intro s hs y hy
    exact neg_ne_zero.mpr
      (smul_ne_zero (hscale s hs).ne' (hboundary y.1 hy))
  have hdeg := D.homotopy_invariant H hcont hnonzero
  have h0 : H 0 = fun y : Metric.closedBall x r => -(t • f y.1) := by
    funext y
    simp only [H, sub_zero, one_mul, add_zero]
  have h1 : H 1 = fun y : Metric.closedBall x r => -f y.1 := by
    funext y
    simp only [H, sub_self, zero_mul, zero_add, one_smul]
  simpa only [h0, h1] using hdeg

end
end PhosphorylationStableCapacity
