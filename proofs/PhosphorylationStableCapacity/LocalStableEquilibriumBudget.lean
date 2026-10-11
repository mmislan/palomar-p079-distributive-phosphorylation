module
public import proofs.PhosphorylationStableCapacity.LocalAsymptoticStability

@[expose] public section

namespace PhosphorylationStableCapacity

open PhosphorylationSharpness

noncomputable section

/-- Literal positive equilibria that are locally asymptotically stable
relative to their fixed compatibility class. -/
def locallyStablePositiveStates {n : ℕ}
    (ET FT ST : ℝ) (k : Rates n) : Set (State n) :=
  {x | x.Positive ∧ InClass ET FT ST x ∧
    IsLocallyAsymptoticallyStableClass ET FT ST k
      (toCoordinateSpace (chart x))}

/-- Even without the index argument, nonlinear local attractors form
a finite subset of the literal positive equilibria and obey the
general `2n` equilibrium budget. -/
theorem locally_stable_positive_states_finite_ncard_le_two_n {n : ℕ}
    (hn : 0 < n) (ET FT ST : ℝ) (hET : 0 < ET) (hFT : 0 < FT)
    (k : Rates n) (hk : k.Positive) :
    (locallyStablePositiveStates ET FT ST k).Finite ∧
      (locallyStablePositiveStates ET FT ST k).ncard ≤ 2*n := by
  let E : Set (State n) :=
    {x | x.Positive ∧ Equilibrium k x ∧ InClass ET FT ST x}
  obtain ⟨hfinite, hbudget⟩ :=
    positive_equilibria_finite_and_ncard_le_two_n
      k hn hk ET FT ST hET hFT
  have hsub : locallyStablePositiveStates ET FT ST k ⊆ E := by
    intro x hx
    rcases hx with ⟨hxpos, hxclass, hxstable⟩
    have hzero : restrictedFieldEuclid ET FT ST k
        (toCoordinateSpace (chart x)) = 0 := hxstable.1
    have heq : Equilibrium k x := by
      have h := (restrictedFieldEuclid_eq_zero_iff ET FT ST k
        (toCoordinateSpace (chart x))).1 hzero
      rw [of_toCoordinateSpace,
        unChart_chart_of_inClass ET FT ST x hxclass] at h
      exact h
    exact ⟨hxpos, heq, hxclass⟩
  exact ⟨hfinite.subset hsub,
    (Set.ncard_le_ncard hsub hfinite).trans hbudget⟩

end
end PhosphorylationStableCapacity
