module
public import proofs.PhosphorylationStableCapacity.SelectedAttractorSphereSmallTime

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section
open PhosphorylationSharpness

/-- A point on a sphere cannot coincide with a convex combination of
the center and a point strictly inside the ball. This is the boundary
homotopy normalizing an inward map to the center map. -/
theorem inward_point_boundary_homotopy {n : ℕ}
    (x y w : CoordinateSpace n) (r : ℝ) (hr : 0 < r)
    (hy : dist y x = r) (hw : dist w x < r) :
    ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 →
      (1 - s) • (y - w) + s • (y - x) ≠ 0 := by
  intro s hs hzero
  have hwball : w ∈ Metric.ball x r := Metric.mem_ball.mpr hw
  have hxball : x ∈ Metric.ball x r := Metric.mem_ball_self hr
  have hcombo := (convex_iff_add_mem).mp (convex_ball x r)
    hwball hxball (sub_nonneg.mpr hs.2) hs.1 (by ring)
  have heq : y = (1 - s) • w + s • x := by
    have hid : (1 - s) • (y - w) + s • (y - x) =
        y - ((1 - s) • w + s • x) := by
      calc
        (1 - s) • (y - w) + s • (y - x) =
            ((1 - s) • y + s • y) -
              ((1 - s) • w + s • x) := by
                simp only [smul_sub]
                abel
        _ = y - ((1 - s) • w + s • x) := by
          rw [← add_smul]
          simp
    exact sub_eq_zero.mp (hid ▸ hzero)
  have hinside : dist y x < r := by
    rw [heq]
    exact Metric.mem_ball.mp hcombo
  exact (lt_irrefl r (hy ▸ hinside))

/-- The inward positive-time flow on the selected isolating sphere
is boundary-homotopic to the center displacement on that sphere. -/
def InwardFlowCenterBoundaryHomotopy {n : ℕ}
    (ET FT ST : ℝ) (hET : 0 < ET)
    (k : Rates n) (hk : k.Positive)
    (x : CoordinateSpace n) (r T : ℝ) : Prop :=
  ∀ z : classPolytope n ET FT ST,
    dist z.1 x = r →
      ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 →
        (1 - s) •
          (z.1 - physicalForwardCurve ET FT ST hET k hk z T) +
          s • (z.1 - x) ≠ 0

theorem selected_sphere_inward_flow_center_homotopy {n : ℕ}
    (ET FT ST : ℝ) (hET : 0 < ET)
    (k : Rates n) (hk : k.Positive)
    (x : CoordinateSpace n) (r T : ℝ) (hr : 0 < r)
    (hinward : ∀ z : classPolytope n ET FT ST,
      dist z.1 x ≤ r →
        dist (physicalForwardCurve ET FT ST hET k hk z T) x < r) :
    InwardFlowCenterBoundaryHomotopy ET FT ST hET k hk x r T := by
  intro z hz
  exact inward_point_boundary_homotopy x z.1
    (physicalForwardCurve ET FT ST hET k hk z T)
    r hr hz (hinward z hz.le)

/-- The no-return property keeps every positive-time flow displacement
nonzero on the selected sphere throughout interpolation of two positive
times. -/
def PositiveTimeFlowBoundaryHomotopy {n : ℕ}
    (ET FT ST : ℝ) (hET : 0 < ET)
    (k : Rates n) (hk : k.Positive)
    (x : CoordinateSpace n) (r t T : ℝ) : Prop :=
  ∀ z : classPolytope n ET FT ST,
    dist z.1 x = r →
      ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 →
        z.1 - physicalForwardCurve ET FT ST hET k hk z
          ((1 - s) * t + s * T) ≠ 0

theorem selected_sphere_positive_time_boundary_homotopy {n : ℕ}
    (ET FT ST : ℝ) (hET : 0 < ET)
    (k : Rates n) (hk : k.Positive)
    (x : CoordinateSpace n) (r t T : ℝ)
    (ht : 0 < t) (hT : 0 < T)
    (hnoReturn : ∀ z : classPolytope n ET FT ST,
      dist z.1 x = r → ∀ u : ℝ, 0 < u →
        physicalForwardCurve ET FT ST hET k hk z u ≠ z.1) :
    PositiveTimeFlowBoundaryHomotopy ET FT ST hET k hk x r t T := by
  intro z hz s hs hzero
  have hu : 0 < (1 - s) * t + s * T := by
    rcases le_total t T with hle | hle
    · have hnonneg : 0 ≤ s * (T - t) :=
        mul_nonneg hs.1 (sub_nonneg.mpr hle)
      nlinarith
    · have hnonneg : 0 ≤ (1 - s) * (t - T) :=
        mul_nonneg (sub_nonneg.mpr hs.2) (sub_nonneg.mpr hle)
      nlinarith
  exact (hnoReturn z hz _ hu) (sub_eq_zero.mp hzero).symm

end
end PhosphorylationStableCapacity
