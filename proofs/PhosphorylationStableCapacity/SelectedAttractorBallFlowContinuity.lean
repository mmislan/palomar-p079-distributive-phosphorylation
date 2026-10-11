module
public import proofs.PhosphorylationStableCapacity.ClassFlowJointContinuity
public import proofs.PhosphorylationStableCapacity.SelectedAttractorSphereInwardHomotopy

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section
open PhosphorylationSharpness

/-- Include a selected closed ball in the physical class using its
certified containment in the strict class interior. -/
def selectedBallToClass {n : ℕ} (ET FT ST : ℝ)
    (x : CoordinateSpace n) (r : ℝ)
    (hinside : Metric.closedBall x r ⊆
      classPolytopeStrict n ET FT ST) :
    Metric.closedBall x r → classPolytope n ET FT ST :=
  fun y => ⟨y.1,
    classPolytopeStrict_subset n ET FT ST (hinside y.2)⟩

theorem selectedBallToClass_continuous {n : ℕ}
    (ET FT ST : ℝ) (x : CoordinateSpace n) (r : ℝ)
    (hinside : Metric.closedBall x r ⊆
      classPolytopeStrict n ET FT ST) :
    Continuous (selectedBallToClass ET FT ST x r hinside) := by
  exact continuous_subtype_val.subtype_mk
    (fun y => classPolytopeStrict_subset n ET FT ST (hinside y.2))

/-- The physical forward flow is jointly continuous on nonnegative
times and the exact closed ball chosen for a local attractor. -/
theorem selectedBallForwardCurve_joint_continuousOn {n : ℕ}
    (ET FT ST : ℝ) (hET : 0 < ET)
    (k : Rates n) (hk : k.Positive)
    (x : CoordinateSpace n) (r : ℝ)
    (hinside : Metric.closedBall x r ⊆
      classPolytopeStrict n ET FT ST) :
    ContinuousOn
      (fun p : ℝ × Metric.closedBall x r =>
        physicalForwardCurve ET FT ST hET k hk
          (selectedBallToClass ET FT ST x r hinside p.2) p.1)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ) := by
  let ι : ℝ × Metric.closedBall x r →
      ℝ × classPolytope n ET FT ST :=
    fun p => (p.1, selectedBallToClass ET FT ST x r hinside p.2)
  have hι : Continuous ι :=
    continuous_fst.prodMk
      ((selectedBallToClass_continuous ET FT ST x r hinside).comp
        continuous_snd)
  have hmaps : Set.MapsTo ι
      (Set.Ici (0 : ℝ) ×ˢ Set.univ)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ) := by
    intro p hp
    exact ⟨hp.1, Set.mem_univ _⟩
  exact (physicalForwardCurve_joint_continuousOn ET FT ST hET k hk).comp
    hι.continuousOn hmaps

/-- The positive-time inward map is an actual self-map of the selected
closed Euclidean ball. -/
def selectedBallTimeMap {n : ℕ}
    (ET FT ST : ℝ) (hET : 0 < ET)
    (k : Rates n) (hk : k.Positive)
    (x : CoordinateSpace n) (r T : ℝ)
    (hinside : Metric.closedBall x r ⊆
      classPolytopeStrict n ET FT ST)
    (hinward : ∀ z : classPolytope n ET FT ST,
      dist z.1 x ≤ r →
        dist (physicalForwardCurve ET FT ST hET k hk z T) x < r) :
    Metric.closedBall x r → Metric.closedBall x r :=
  fun y => ⟨physicalForwardCurve ET FT ST hET k hk
      (selectedBallToClass ET FT ST x r hinside y) T,
    Metric.mem_closedBall.mpr
      (le_of_lt (hinward _ (Metric.mem_closedBall.mp y.2)))⟩

theorem selectedBallTimeMap_continuous {n : ℕ}
    (ET FT ST : ℝ) (hET : 0 < ET)
    (k : Rates n) (hk : k.Positive)
    (x : CoordinateSpace n) (r T : ℝ) (hT : 0 ≤ T)
    (hinside : Metric.closedBall x r ⊆
      classPolytopeStrict n ET FT ST)
    (hinward : ∀ z : classPolytope n ET FT ST,
      dist z.1 x ≤ r →
        dist (physicalForwardCurve ET FT ST hET k hk z T) x < r) :
    Continuous (selectedBallTimeMap ET FT ST hET k hk x r T
      hinside hinward) := by
  have hflow : Continuous (fun y : Metric.closedBall x r =>
      physicalForwardCurve ET FT ST hET k hk
        (selectedBallToClass ET FT ST x r hinside y) T) := by
    change Continuous (fun y : Metric.closedBall x r =>
      (physicalTimeMap ET FT ST hET k hk T hT
        (selectedBallToClass ET FT ST x r hinside y) :
          CoordinateSpace n))
    exact continuous_subtype_val.comp
      ((physicalTimeMap_continuous ET FT ST hET k hk T hT).comp
        (selectedBallToClass_continuous ET FT ST x r hinside))
  exact hflow.subtype_mk
    (fun y => Metric.mem_closedBall.mpr
      (le_of_lt (hinward _ (Metric.mem_closedBall.mp y.2))))

end
end PhosphorylationStableCapacity
