module
public import proofs.PhosphorylationStableCapacity.ClassPhysicalForwardFlow

@[expose] public section

namespace PhosphorylationStableCapacity

open PhosphorylationSharpness Filter
open scoped Topology

noncomputable section

/-- The forward-existence clause in the nonlinear class-stability
predicate holds near every strict interior class state. -/
theorem positive_class_nearby_forward_existence {n : ℕ}
    (ET FT ST : ℝ) (hET : 0 < ET)
    (k : Rates n) (hk : k.Positive)
    (x : CoordinateSpace n)
    (hx : x ∈ classPolytopeStrict n ET FT ST) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ y : CoordinateSpace n, dist y x < δ →
        ∃ γ, IsForwardClassCurve
          (restrictedFieldEuclid ET FT ST k) y γ := by
  have hnhds : classPolytopeStrict n ET FT ST ∈ 𝓝 x :=
    (classPolytopeStrict_isOpen n ET FT ST).mem_nhds hx
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp hnhds
  refine ⟨δ, hδ, ?_⟩
  intro y hy
  have hystrict : y ∈ classPolytopeStrict n ET FT ST :=
    hball (Metric.mem_ball.mpr hy)
  obtain ⟨γ, hγ, _⟩ :=
    exists_physical_forward_class_curve ET FT ST hET k hk y
      ((classPolytopeStrict_subset n ET FT ST) hystrict)
  exact ⟨γ, hγ⟩

/-- In particular, the forward-existence clause holds near the chart
point of any literal positive state in its fixed compatibility class. -/
theorem positive_state_nearby_forward_existence {n : ℕ}
    (ET FT ST : ℝ) (hET : 0 < ET)
    (k : Rates n) (hk : k.Positive)
    (x : State n) (hx : x.Positive)
    (hclass : InClass ET FT ST x) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ y : CoordinateSpace n,
        dist y (toCoordinateSpace (chart x)) < δ →
          ∃ γ, IsForwardClassCurve
            (restrictedFieldEuclid ET FT ST k) y γ :=
  positive_class_nearby_forward_existence ET FT ST hET k hk
    (toCoordinateSpace (chart x))
    (positive_state_mem_classPolytopeStrict ET FT ST x hx hclass)

end
end PhosphorylationStableCapacity
