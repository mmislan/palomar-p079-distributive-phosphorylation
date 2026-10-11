module
public import proofs.PhosphorylationStableCapacity.LoadedStateChartBridge
public import proofs.PhosphorylationStableCapacity.CoalescedFiniteSource

@[expose] public section

namespace PhosphorylationStableCapacity

open Filter PhosphorylationSharpness

noncomputable section

/-- The actual positive coalesced equilibrium is exactly the state at its
loaded class coordinates under its one conserved-total triple. -/
theorem coalescedLoadedChartBase_eventually_eq_state (m : ℕ) :
    ∀ᶠ r : ℝ in atTop,
      stateFromLoaded (2 * r) 2 (2 * (r + 1))
        (loadedCoordOfState (coalescedFiniteState (m + 1) r)) =
          coalescedFiniteState (m + 1) r := by
  filter_upwards [coalescedFiniteState_eventually_equilibrium (m + 1)]
    with r hsource
  obtain ⟨_, _, _, hE, hF, hS⟩ := hsource
  exact stateFromLoaded_loadedCoordOfState (2 * r) 2
    (2 * (r + 1)) (coalescedFiniteState (m + 1) r)
    ⟨hE, hF, hS⟩

end
end PhosphorylationStableCapacity
