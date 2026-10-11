module
public import proofs.PhosphorylationStableCapacity.SelectedBallEquilibriumZero

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section
open PhosphorylationSharpness

/-- The reconstruction map is injective on all selected-ball
coordinates, independently of the equilibrium equation. -/
theorem selected_ball_reconstruction_injective {n : ℕ}
    (ET FT ST : ℝ) (x : CoordinateSpace n) (r : ℝ) :
    Function.Injective
      (fun y : Metric.closedBall x r =>
        unChart ET FT ST (ofCoordinateSpace y.1)) := by
  intro a b hab
  apply Subtype.ext
  have h := congrArg (fun z : State n =>
      toCoordinateSpace (chart z)) hab
  simpa only [chart_unChart, to_ofCoordinateSpace] using h

/-- A finite set of all positive class equilibria makes the exact
selected-ball zero set finite through the injective literal chart. -/
theorem finite_selected_ball_zeros {n : ℕ}
    (ET FT ST : ℝ) (k : Rates n)
    (x : CoordinateSpace n) (r : ℝ)
    (hinside : Metric.closedBall x r ⊆
      classPolytopeStrict n ET FT ST)
    (E : Set (State n))
    (hE : E = {z | z.Positive ∧ Equilibrium k z ∧ InClass ET FT ST z})
    (hfinite : E.Finite) :
    {y : Metric.closedBall x r |
      restrictedFieldEuclid ET FT ST k y.1 = 0}.Finite := by
  apply Set.Finite.of_injOn
    (t := E)
    (f := fun y : Metric.closedBall x r =>
      unChart ET FT ST (ofCoordinateSpace y.1))
  · intro y hy
    rw [hE]
    exact (selected_ball_zero_iff_positive_equilibrium
      ET FT ST k x r hinside y).mp hy
  · exact (selected_ball_reconstruction_injective ET FT ST x r).injOn
  · exact hfinite

end
end PhosphorylationStableCapacity
