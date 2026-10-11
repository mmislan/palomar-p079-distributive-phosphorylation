module
public import proofs.PhosphorylationStableCapacity.SelectedAttractorBallFlowContinuity

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section

/-- A conditional degree interface for maps on one closed Euclidean
ball. The construction and proof of these axioms are the outstanding
topological task; this structure is not an implementation of degree. -/
structure ClosedBallDegree (n : ℕ) (x : CoordinateSpace n) (r : ℝ) where
  degree : (Metric.closedBall x r → CoordinateSpace n) → ℤ
  homotopy_invariant :
    ∀ (H : ℝ → Metric.closedBall x r → CoordinateSpace n),
      ContinuousOn (fun p : ℝ × Metric.closedBall x r => H p.1 p.2)
        (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ) →
      (∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 →
        ∀ y : Metric.closedBall x r, dist y.1 x = r → H s y ≠ 0) →
      degree (H 0) = degree (H 1)
  center_normalization :
    degree (fun y : Metric.closedBall x r => y.1 - x) = 1
  regular_zero_sum :
    ∀ (f : CoordinateSpace n → CoordinateSpace n)
      (_hf : Differentiable ℝ f)
      (Z : Finset (Metric.closedBall x r)),
      (∀ y : Metric.closedBall x r, f y.1 = 0 ↔ y ∈ Z) →
      (∀ y : Metric.closedBall x r, dist y.1 x = r → f y.1 ≠ 0) →
      (∀ y ∈ Z,
        LinearMap.det (fderiv ℝ f y.1).toLinearMap ≠ 0) →
      degree (fun y : Metric.closedBall x r => f y.1) =
        ∑ y ∈ Z,
          if 0 < LinearMap.det (fderiv ℝ f y.1).toLinearMap
          then (1 : ℤ) else -1

/-- Any continuous self-map that sends the entire closed ball strictly
inside has degree one for its identity-minus-map displacement, provided
a genuine boundary-homotopy-invariant degree is supplied. -/
theorem closedBallDegree_inward_map_eq_one {n : ℕ}
    (x : CoordinateSpace n) (r : ℝ) (hr : 0 < r)
    (D : ClosedBallDegree n x r)
    (F : Metric.closedBall x r → Metric.closedBall x r)
    (hF : Continuous F)
    (hinward : ∀ y : Metric.closedBall x r, dist (F y).1 x < r) :
    D.degree (fun y => y.1 - (F y).1) = 1 := by
  let H : ℝ → Metric.closedBall x r → CoordinateSpace n :=
    fun s y => (1 - s) • (y.1 - (F y).1) + s • (y.1 - x)
  have hcont : ContinuousOn
      (fun p : ℝ × Metric.closedBall x r => H p.1 p.2)
      (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ) := by
    have h : Continuous (fun p : ℝ × Metric.closedBall x r =>
        (1 - p.1) • (p.2.1 - (F p.2).1) +
          p.1 • (p.2.1 - x)) := by
      fun_prop
    exact h.continuousOn
  have hboundary : ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 →
      ∀ y : Metric.closedBall x r, dist y.1 x = r → H s y ≠ 0 := by
    intro s hs y hy
    exact inward_point_boundary_homotopy x y.1 (F y).1 r hr
      hy (hinward y) s hs
  have heq := D.homotopy_invariant H hcont hboundary
  simpa [H, D.center_normalization] using heq

/-- The selected P079 inward flow map has degree one under the
conditional closed-ball degree interface. No degree construction is
asserted here. -/
theorem selectedBallTimeMap_degree_one {n : ℕ}
    (ET FT ST : ℝ) (hET : 0 < ET)
    (k : PhosphorylationSharpness.Rates n)
    (hk : k.Positive)
    (x : CoordinateSpace n) (r T : ℝ)
    (hr : 0 < r) (hT : 0 ≤ T)
    (hinside : Metric.closedBall x r ⊆
      classPolytopeStrict n ET FT ST)
    (hinward : ∀ z : classPolytope n ET FT ST,
      dist z.1 x ≤ r →
        dist (physicalForwardCurve ET FT ST hET k hk z T) x < r)
    (D : ClosedBallDegree n x r) :
    D.degree (fun y => y.1 -
      (selectedBallTimeMap ET FT ST hET k hk x r T
        hinside hinward y).1) = 1 := by
  apply closedBallDegree_inward_map_eq_one x r hr D
    (selectedBallTimeMap ET FT ST hET k hk x r T
      hinside hinward)
    (selectedBallTimeMap_continuous ET FT ST hET k hk x r T hT
      hinside hinward)
  intro y
  exact hinward _ (Metric.mem_closedBall.mp y.2)

end
end PhosphorylationStableCapacity
