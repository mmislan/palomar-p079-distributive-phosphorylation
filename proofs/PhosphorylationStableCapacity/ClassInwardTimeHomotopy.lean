module
public import proofs.PhosphorylationStableCapacity.ClassFlowJointContinuity

@[expose] public section

namespace PhosphorylationStableCapacity

open PhosphorylationSharpness

noncomputable section

/-- Joint continuity of the affine homotopy from a fixed physical
time map to a constant class-coordinate center. -/
theorem physical_inward_homotopy_continuous {n : ℕ}
    (ET FT ST : ℝ) (hET : 0 < ET)
    (k : Rates n) (hk : k.Positive)
    (x : CoordinateSpace n) (T : ℝ) (hT : 0 ≤ T) :
    Continuous (fun p : ℝ × classPolytope n ET FT ST =>
      (1 - p.1) • physicalForwardCurve ET FT ST hET k hk p.2 T +
        p.1 • x) := by
  have hflow : Continuous
      (fun z : classPolytope n ET FT ST =>
        physicalForwardCurve ET FT ST hET k hk z T) := by
    change Continuous
      (fun z : classPolytope n ET FT ST =>
        (physicalTimeMap ET FT ST hET k hk T hT z : CoordinateSpace n))
    exact continuous_subtype_val.comp
      (physicalTimeMap_continuous ET FT ST hET k hk T hT)
  exact ((continuous_const.sub continuous_fst).smul
    (hflow.comp continuous_snd)).add
    (continuous_fst.smul continuous_const)

/-- A straight-line homotopy from the inward physical time map to the
constant center still sends every point of the closed class ball into
its open ambient-coordinate ball. This is the zero-free boundary
homotopy required by the fixed-point-index route. -/
theorem local_attractor_inward_time_homotopy {n : ℕ}
    (ET FT ST : ℝ) (hET : 0 < ET)
    (k : Rates n) (hk : k.Positive)
    (x : CoordinateSpace n)
    (hx : IsLocallyAsymptoticallyStableClass ET FT ST k x)
    (hxmem : x ∈ classPolytope n ET FT ST) :
    ∃ r : ℝ, 0 < r ∧ ∃ T : ℝ, 0 ≤ T ∧
      ∀ z ∈ Metric.closedBall (⟨x, hxmem⟩ :
          classPolytope n ET FT ST) r,
        ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 →
          dist ((1 - s) • physicalForwardCurve ET FT ST hET k hk z T +
            s • x) x < r := by
  obtain ⟨r, hr, T, hT, hinward⟩ :=
    local_attractor_inward_time_map ET FT ST hET k hk x hx hxmem
  refine ⟨r, hr, T, hT, ?_⟩
  intro z hz s hs
  have hflow : physicalForwardCurve ET FT ST hET k hk z T ∈
      Metric.ball x r := Metric.mem_ball.mpr (hinward z hz)
  have hcenter : x ∈ Metric.ball x r := Metric.mem_ball_self hr
  have hcombo := (convex_iff_add_mem).mp (convex_ball x r)
    hflow hcenter (sub_nonneg.mpr hs.2) hs.1 (by ring)
  exact Metric.mem_ball.mp hcombo

end
end PhosphorylationStableCapacity
