module
public import proofs.PhosphorylationStableCapacity.SelectedBallDegreeRegularFormula
public import proofs.PhosphorylationStableCapacity.AttractorRateBoundaryPersistence

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section
open PhosphorylationSharpness

/-- Under the conditional closed-ball degree interface, the exact
zero-free rate homotopy preserves the degree of the negative literal
field on the selected ball, including singular intermediate slices. -/
theorem selected_ball_degree_eq_of_rate_homotopy {n : ℕ}
    (ET FT ST : ℝ) (k k' : Rates n)
    (x : CoordinateSpace n) (r : ℝ)
    (D : ClosedBallDegree n x r)
    (hboundary : ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 →
      ∀ y : CoordinateSpace n, dist y x = r →
        restrictedFieldEuclid ET FT ST
          (ratesFromVector
            (rateVector k + t • (rateVector k' - rateVector k))) y ≠ 0) :
    D.degree (fun y : Metric.closedBall x r =>
      -restrictedFieldEuclid ET FT ST k y.1) =
    D.degree (fun y : Metric.closedBall x r =>
      -restrictedFieldEuclid ET FT ST k' y.1) := by
  let H : ℝ → Metric.closedBall x r → CoordinateSpace n :=
    fun t y => -restrictedFieldEuclid ET FT ST
      (ratesFromVector
        (rateVector k + t • (rateVector k' - rateVector k))) y.1
  have hcont : ContinuousOn
      (fun p : ℝ × Metric.closedBall x r => H p.1 p.2)
      (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ) := by
    have hmap : Continuous
        (fun p : ℝ × Metric.closedBall x r =>
          (p.1, p.2.1)) := by
      fun_prop
    have h : Continuous
        (fun p : ℝ × Metric.closedBall x r => H p.1 p.2) := by
      exact ((continuous_restricted_field_rate_homotopy
        ET FT ST k (rateVector k')).comp hmap).neg
    exact h.continuousOn
  have hnonzero : ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 →
      ∀ y : Metric.closedBall x r,
        dist y.1 x = r → H t y ≠ 0 := by
    intro t ht y hy
    exact neg_ne_zero.mpr (hboundary t ht y.1 hy)
  have hdeg := D.homotopy_invariant H hcont hnonzero
  have h0 : H 0 = fun y : Metric.closedBall x r =>
      -restrictedFieldEuclid ET FT ST k y.1 := by
    funext y
    simp only [H, zero_smul, add_zero, ratesFromVector_rateVector]
  have h1 : H 1 = fun y : Metric.closedBall x r =>
      -restrictedFieldEuclid ET FT ST k' y.1 := by
    funext y
    have hv : rateVector k + (rateVector k' - rateVector k) =
        rateVector k' := by abel
    simp only [H, one_smul, hv, ratesFromVector_rateVector]
  simpa only [h0, h1] using hdeg

end
end PhosphorylationStableCapacity
