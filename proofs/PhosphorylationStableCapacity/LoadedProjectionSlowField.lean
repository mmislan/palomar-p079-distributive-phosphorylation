module
public import proofs.PhosphorylationStableCapacity.LoadedStateChartDerivative
public import proofs.PhosphorylationStableCapacity.LoadedReducedField

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section
open PhosphorylationSharpness

/-- Projecting a literal state into any fixed loaded class preserves every
loaded-level velocity exactly: those velocities use only catalytic currents
and the projection leaves both complex lists unchanged. -/
theorem loadedLevel_field_projection_eq {n : ℕ}
    (ET FT ST : ℝ) (k : Rates n) (x : State n)
    (j : Fin (n + 1)) :
    loadedLevel
        (field k (stateFromLoaded ET FT ST (loadedCoordOfState x))) j =
      loadedLevel (field k x) j := by
  simp only [loadedLevel_field_eq_catalytic_flux,
    stateFromLoaded_loadedCoordOfState_C,
    stateFromLoaded_loadedCoordOfState_D]

/-- The slow component of the literal fixed-class loaded field agrees
pointwise with the loaded velocity of the original state. -/
theorem loadedRestrictedField_coordOfState_slow {n : ℕ}
    (ET FT ST : ℝ) (k : Rates n) (x : State n)
    (i : Fin n) :
    (loadedRestrictedField ET FT ST k (loadedCoordOfState x)).1 i =
      loadedLevel (field k x) i.succ := by
  rw [loadedRestrictedField_slow]
  exact loadedLevel_field_projection_eq ET FT ST k x i.succ

/-- In particular, this field component is exactly the literal reduced
binding-manifold slow field at every substrate state. -/
theorem loadedRestrictedField_bindingState_slow {n : ℕ}
    (ET FT ST : ℝ) (p q : Fin (n + 1) → ℝ)
    (k : Rates n) (S : Fin (n + 1) → ℝ) (i : Fin n) :
    (loadedRestrictedField ET FT ST k
      (loadedCoordOfState (bindingState ET FT p q S))).1 i =
        bindingReducedSlowField ET FT p q k S i.succ := by
  exact loadedRestrictedField_coordOfState_slow ET FT ST k
    (bindingState ET FT p q S) i

end
end PhosphorylationStableCapacity
