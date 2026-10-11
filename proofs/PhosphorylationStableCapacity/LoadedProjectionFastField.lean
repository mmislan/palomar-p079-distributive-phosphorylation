module
public import proofs.PhosphorylationStableCapacity.LoadedStateChartDefect
public import proofs.PhosphorylationStableCapacity.LoadedFastField

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section
open PhosphorylationSharpness

/-- The exact kinase-complex field error caused by projecting an arbitrary
literal state into a fixed compatibility class. -/
theorem loadedProjectionFastField_C {n : ℕ}
    (ET FT ST : ℝ) (k : Rates n) (x : State n) (i : Fin n) :
    (loadedRestrictedField ET FT ST k (loadedCoordOfState x)).2.1 i =
      (field k x).C i +
        k.a i * (
          (stateFromLoaded ET FT ST (loadedCoordOfState x)).S i.castSucc *
            (ET - totalE x) +
          ((stateFromLoaded ET FT ST (loadedCoordOfState x)).S i.castSucc -
            x.S i.castSucc) * x.E) := by
  rw [loadedFastField_C]
  rw [stateFromLoaded_loadedCoordOfState_E,
    stateFromLoaded_loadedCoordOfState_C]
  simp only [field, kinaseNet]
  ring

/-- The phosphatase-complex field error has just one factor: the error
in the prescribed phosphatase total. -/
theorem loadedProjectionFastField_D {n : ℕ}
    (ET FT ST : ℝ) (k : Rates n) (x : State n) (i : Fin n) :
    (loadedRestrictedField ET FT ST k (loadedCoordOfState x)).2.2 i =
      (field k x).D i +
        k.alpha i * x.S i.succ * (FT - totalF x) := by
  rw [loadedFastField_D]
  rw [stateFromLoaded_loadedCoordOfState_F,
    stateFromLoaded_loadedCoordOfState_D,
    stateFromLoaded_loadedCoordOfState_S_succ]
  simp only [field, phosphataseNet]
  ring

end
end PhosphorylationStableCapacity
