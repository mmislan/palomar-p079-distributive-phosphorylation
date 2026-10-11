module
public import proofs.PhosphorylationStableCapacity.NegativeFieldDeterminantBridge

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section
open PhosphorylationSharpness

/-- Every strict class coordinate reconstructs a positive literal
state with the prescribed conserved totals. -/
theorem positive_unChart_of_strict_coordinate {n : ℕ}
    (ET FT ST : ℝ) (u : CoordinateSpace n)
    (hu : u ∈ classPolytopeStrict n ET FT ST) :
    (unChart ET FT ST (ofCoordinateSpace u)).Positive := by
  rcases hu with ⟨hS, hC, hD, hST, hET, hFT⟩
  unfold State.Positive
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro i
    refine Fin.cases ?_ ?_ i
    · dsimp [unChart, ofCoordinateSpace]
      linarith
    · intro j
      simpa only [unChart, ofCoordinateSpace, Fin.cases_succ] using hS j
  · dsimp [unChart, ofCoordinateSpace]
    linarith
  · dsimp [unChart, ofCoordinateSpace]
    linarith
  · exact hC
  · exact hD

/-- In the selected ball, zeros of the literal restricted field are
exactly positive equilibria in the specified compatibility class. -/
theorem selected_ball_zero_iff_positive_equilibrium {n : ℕ}
    (ET FT ST : ℝ) (k : Rates n)
    (x : CoordinateSpace n) (r : ℝ)
    (hinside : Metric.closedBall x r ⊆
      classPolytopeStrict n ET FT ST)
    (y : Metric.closedBall x r) :
    restrictedFieldEuclid ET FT ST k y.1 = 0 ↔
      (unChart ET FT ST (ofCoordinateSpace y.1)).Positive ∧
      Equilibrium k (unChart ET FT ST (ofCoordinateSpace y.1)) ∧
      InClass ET FT ST
        (unChart ET FT ST (ofCoordinateSpace y.1)) := by
  constructor
  · intro hy
    exact ⟨positive_unChart_of_strict_coordinate ET FT ST y.1
        (hinside y.2),
      (restrictedFieldEuclid_eq_zero_iff ET FT ST k y.1).mp hy,
      unChart_inClass ET FT ST (ofCoordinateSpace y.1)⟩
  · rintro ⟨_, heq, _⟩
    exact (restrictedFieldEuclid_eq_zero_iff ET FT ST k y.1).mpr heq

end
end PhosphorylationStableCapacity
