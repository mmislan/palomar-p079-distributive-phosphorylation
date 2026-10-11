module
public import proofs.PhosphorylationStableCapacity.ClosedBallDegreeInterface
public import proofs.PhosphorylationStableCapacity.ClosedBallDegreeInstance435

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section

/-- The isolated 4.35 degree construction supplies the exact model-side
closed-ball degree interface at every positive radius. -/
theorem closedBallDegree_exists_435
    (n : ℕ) (x : CoordinateSpace n) (r : ℝ) (hr : 0 < r) :
    Nonempty (ClosedBallDegree n x r) := by
  obtain ⟨D⟩ :=
    Topology435.coordinateClosedBallDegree435_all_exists n x r hr
  exact ⟨{
    degree := D.degree
    homotopy_invariant := D.homotopy_invariant
    center_normalization := D.center_normalization
    regular_zero_sum := D.regular_zero_sum }⟩

end

end PhosphorylationStableCapacity
