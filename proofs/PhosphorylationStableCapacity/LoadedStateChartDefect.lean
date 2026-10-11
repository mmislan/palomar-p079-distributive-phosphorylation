module
public import proofs.PhosphorylationStableCapacity.LoadedStateChartBridge

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section
open PhosphorylationSharpness

/-- Projecting an arbitrary state to a named loaded class first forgets
its existing totals and rebuilds the state from its class coordinates. -/
theorem stateFromLoaded_loadedCoordOfState_eq_unChart {n : ℕ}
    (ET FT ST : ℝ) (x : State n) :
    stateFromLoaded ET FT ST (loadedCoordOfState x) =
      unChart ET FT ST (chart x) := by
  change unChart ET FT ST
    (ofCoordinateSpace (fromLoadedCoord
      (toLoadedCoord (toCoordinateSpace (chart x))))) = _
  rw [from_toLoadedCoord, of_toCoordinateSpace]

/-- Its free kinase difference is exactly the error in the prescribed
kinase total. -/
theorem stateFromLoaded_loadedCoordOfState_E {n : ℕ}
    (ET FT ST : ℝ) (x : State n) :
    (stateFromLoaded ET FT ST (loadedCoordOfState x)).E =
      x.E + (ET - totalE x) := by
  rw [stateFromLoaded_loadedCoordOfState_eq_unChart]
  change ET - (∑ i : Fin n, x.C i) = x.E + (ET - totalE x)
  simp only [totalE]
  ring

/-- Its free phosphatase difference is the phosphatase-total error. -/
theorem stateFromLoaded_loadedCoordOfState_F {n : ℕ}
    (ET FT ST : ℝ) (x : State n) :
    (stateFromLoaded ET FT ST (loadedCoordOfState x)).F =
      x.F + (FT - totalF x) := by
  rw [stateFromLoaded_loadedCoordOfState_eq_unChart]
  change FT - (∑ i : Fin n, x.D i) = x.F + (FT - totalF x)
  simp only [totalF]
  ring

/-- Its free substrate at level zero absorbs the entire substrate-total
error; all later free-substrate levels are unchanged. -/
theorem stateFromLoaded_loadedCoordOfState_S_zero {n : ℕ}
    (ET FT ST : ℝ) (x : State n) :
    (stateFromLoaded ET FT ST (loadedCoordOfState x)).S 0 =
      x.S 0 + (ST - totalS x) := by
  rw [stateFromLoaded_loadedCoordOfState_eq_unChart]
  change ST - (∑ i : Fin n, x.S i.succ) -
      (∑ i : Fin n, x.C i) - (∑ i : Fin n, x.D i) =
        x.S 0 + (ST - totalS x)
  simp only [totalS, Fin.sum_univ_succ]
  ring

theorem stateFromLoaded_loadedCoordOfState_S_succ {n : ℕ}
    (ET FT ST : ℝ) (x : State n) (i : Fin n) :
    (stateFromLoaded ET FT ST (loadedCoordOfState x)).S i.succ =
      x.S i.succ := by
  rw [stateFromLoaded_loadedCoordOfState_eq_unChart]
  rfl

theorem stateFromLoaded_loadedCoordOfState_C {n : ℕ}
    (ET FT ST : ℝ) (x : State n) (i : Fin n) :
    (stateFromLoaded ET FT ST (loadedCoordOfState x)).C i = x.C i := by
  rw [stateFromLoaded_loadedCoordOfState_eq_unChart]
  rfl

theorem stateFromLoaded_loadedCoordOfState_D {n : ℕ}
    (ET FT ST : ℝ) (x : State n) (i : Fin n) :
    (stateFromLoaded ET FT ST (loadedCoordOfState x)).D i = x.D i := by
  rw [stateFromLoaded_loadedCoordOfState_eq_unChart]
  rfl

end
end PhosphorylationStableCapacity
