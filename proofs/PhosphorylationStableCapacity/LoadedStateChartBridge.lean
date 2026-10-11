module
public import proofs.PhosphorylationStableCapacity.LoadedFastField

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section
open PhosphorylationSharpness

/-- Read a literal state in the loaded class coordinates, using its free
substrates and complex concentrations. -/
def loadedCoordOfState {n : ℕ} (x : State n) : CoordinateSpace n :=
  toLoadedCoord (toCoordinateSpace (chart x))

/-- For a state in the named compatibility class, the loaded chart
reconstructs that state exactly. -/
theorem stateFromLoaded_loadedCoordOfState {n : ℕ}
    (ET FT ST : ℝ) (x : State n) (hx : InClass ET FT ST x) :
    stateFromLoaded ET FT ST (loadedCoordOfState x) = x := by
  change unChart ET FT ST
    (ofCoordinateSpace (fromLoadedCoord
      (toLoadedCoord (toCoordinateSpace (chart x))))) = x
  rw [from_toLoadedCoord, of_toCoordinateSpace]
  exact unChart_chart_of_inClass ET FT ST x hx

/-- The slow loaded coordinate is the literal inventory at each nonzero
substrate level, even before imposing a compatibility class. -/
theorem loadedCoordOfState_slow {n : ℕ} (x : State n) (i : Fin n) :
    (loadedCoordOfState x).1 i = loadedLevel x i.succ := by
  simp [loadedCoordOfState, toLoadedCoord, toCoordinateSpace,
    chart, boundComplexAt, loadedLevel]
  ring

theorem loadedCoordOfState_C {n : ℕ} (x : State n) (i : Fin n) :
    (loadedCoordOfState x).2.1 i = x.C i := rfl

theorem loadedCoordOfState_D {n : ℕ} (x : State n) (i : Fin n) :
    (loadedCoordOfState x).2.2 i = x.D i := rfl

end
end PhosphorylationStableCapacity
