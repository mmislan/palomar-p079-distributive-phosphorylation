module
public import proofs.PhosphorylationStableCapacity.HurwitzNonlinearStability
public import proofs.PhosphorylationStableCapacity.ClassPolytopeTopology

@[expose] public section

namespace PhosphorylationStableCapacity
noncomputable section
open PhosphorylationSharpness

/-- Attach nonlinear class stability directly to a literal positive state
with its actual Hurwitz class Jacobian, retaining the rates and totals. -/
theorem state_linearly_stable_locally_asymptotically_stable
    {n : ℕ} (hn : 1 ≤ n) (ET FT ST : ℝ) (hET : 0 < ET)
    (k : Rates n) (hk : k.Positive) (s : State n)
    (hs : s.Positive) (heq : Equilibrium k s)
    (hclass : InClass ET FT ST s)
    (hstable : IsLinearlyStable ET FT ST k
      (toCoordinateSpace (chart s))) :
    IsLocallyAsymptoticallyStableClass ET FT ST k
      (toCoordinateSpace (chart s)) := by
  have hfield : restrictedFieldEuclid ET FT ST k
      (toCoordinateSpace (chart s)) = 0 := by
    apply (restrictedFieldEuclid_eq_zero_iff ET FT ST k
      (toCoordinateSpace (chart s))).2
    rw [of_toCoordinateSpace, unChart_chart_of_inClass ET FT ST s hclass]
    exact heq
  exact isLinearlyStable_locally_asymptotically_stable
    hn ET FT ST hET k hk (toCoordinateSpace (chart s))
    (positive_state_mem_classPolytopeStrict ET FT ST s hs hclass)
    hfield hstable

end
end PhosphorylationStableCapacity
