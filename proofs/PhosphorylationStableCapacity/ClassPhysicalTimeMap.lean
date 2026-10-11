module
public import proofs.PhosphorylationStableCapacity.ClassFlowContinuousDependence
public import proofs.PhosphorylationStableCapacity.ClassPhysicalForwardFlow

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section

open PhosphorylationSharpness
open scoped NNReal

/-- One canonical global forward curve through each physical class
state. Uniqueness is proved separately; this choice fixes a time map. -/
def physicalForwardCurve {n : ℕ}
    (ET FT ST : ℝ) (hET : 0 < ET)
    (k : Rates n) (hk : k.Positive)
    (u : classPolytope n ET FT ST) :
    ℝ → CoordinateSpace n :=
  Classical.choose
    (exists_physical_forward_class_curve ET FT ST hET k hk u.1 u.2)

theorem physicalForwardCurve_spec {n : ℕ}
    (ET FT ST : ℝ) (hET : 0 < ET)
    (k : Rates n) (hk : k.Positive)
    (u : classPolytope n ET FT ST) :
    IsForwardClassCurve (restrictedFieldEuclid ET FT ST k) u.1
      (physicalForwardCurve ET FT ST hET k hk u) ∧
    ∀ t : ℝ, 0 ≤ t →
      physicalForwardCurve ET FT ST hET k hk u t ∈
        classPolytope n ET FT ST :=
  Classical.choose_spec
    (exists_physical_forward_class_curve ET FT ST hET k hk u.1 u.2)

/-- The physical time map at any nonnegative time, taking class states
back into the same compact nonnegative class. -/
def physicalTimeMap {n : ℕ}
    (ET FT ST : ℝ) (hET : 0 < ET)
    (k : Rates n) (hk : k.Positive)
    (T : ℝ) (hT : 0 ≤ T) :
    classPolytope n ET FT ST → classPolytope n ET FT ST :=
  fun u => ⟨physicalForwardCurve ET FT ST hET k hk u T,
    (physicalForwardCurve_spec ET FT ST hET k hk u).2 T hT⟩

/-- Grönwall's bound makes each physical time map Lipschitz in its
initial state. This supplies the continuous time maps used in the
nonhyperbolic local-index argument. -/
theorem physicalTimeMap_continuous {n : ℕ}
    (ET FT ST : ℝ) (hET : 0 < ET)
    (k : Rates n) (hk : k.Positive)
    (T : ℝ) (hT : 0 ≤ T) :
    Continuous (physicalTimeMap ET FT ST hET k hk T hT) := by
  obtain ⟨K, hK⟩ :=
    exists_forward_class_curve_exponential_bound ET FT ST k
  let L : ℝ≥0 := ⟨Real.exp ((K : ℝ) * T), Real.exp_pos _ |>.le⟩
  have hL : (L : ℝ) = Real.exp ((K : ℝ) * T) := by
    rfl
  have hLip : LipschitzWith L
      (physicalTimeMap ET FT ST hET k hk T hT) := by
    apply LipschitzWith.of_dist_le_mul
    intro u v
    have hu := physicalForwardCurve_spec ET FT ST hET k hk u
    have hv := physicalForwardCurve_spec ET FT ST hET k hk v
    have hb := hK u.1 v.1
      (physicalForwardCurve ET FT ST hET k hk u)
      (physicalForwardCurve ET FT ST hET k hk v)
      hu.1 hv.1 hu.2 hv.2 T hT
    simpa [physicalTimeMap, Subtype.dist_eq, hL,
      mul_comm] using hb
  exact hLip.continuous

end
end PhosphorylationStableCapacity
