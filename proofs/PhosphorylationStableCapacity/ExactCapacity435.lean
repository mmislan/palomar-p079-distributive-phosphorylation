module
public import proofs.PhosphorylationStableCapacity.ClosedBallDegreeDocking
public import proofs.PhosphorylationStableCapacity.ClosedBallDegreeBridge435

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section

/-- The separately constructed 4.35 closed-ball degree discharges the
model's only remaining topological existence premise. -/
theorem closedBallDegreeExists_435 : ClosedBallDegreeExists :=
  closedBallDegree_exists_435

/-- The unconditional exact stable-state capacity, with the analytic
model and topological degree construction checked by one Lean kernel. -/
theorem all_size_exact_capacity_435
    (n : ℕ) (hn : 1 ≤ n) :
    ExactNonlinearStableCapacity n :=
  all_size_exact_capacity_of_closedBallDegree
    closedBallDegreeExists_435 n hn

/-- The exact capacity assertion with finiteness explicitly included.
For infinite sets, `Set.ncard` alone does not state a cardinality bound. -/
def ExactNonlinearStableCapacityFinite (n : ℕ) : Prop :=
  NonlinearlyStableClassAttains n n ∧
    ∀ (ET FT ST : ℝ), 0 < ET → 0 < FT → 0 < ST →
      ∀ (k : PhosphorylationSharpness.Rates n), k.Positive →
        (locallyStablePositiveStates ET FT ST k).Finite ∧
        (locallyStablePositiveStates ET FT ST k).ncard ≤ n

/-- The fully explicit capacity endpoint: the universal stable-state set
is finite as well as bounded by `n`. -/
theorem all_size_exact_capacity_finite_435
    (n : ℕ) (hn : 1 ≤ n) :
    ExactNonlinearStableCapacityFinite n := by
  obtain ⟨hattain, hceiling⟩ := all_size_exact_capacity_435 n hn
  refine ⟨hattain, ?_⟩
  intro ET FT ST hET hFT hST k hk
  exact ⟨(locally_stable_positive_states_finite_ncard_le_two_n
      hn ET FT ST hET hFT k hk).1,
    hceiling ET FT ST hET hFT hST k hk⟩

end

end PhosphorylationStableCapacity
