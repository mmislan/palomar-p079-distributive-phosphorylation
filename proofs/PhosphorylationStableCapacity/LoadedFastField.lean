module
public import proofs.PhosphorylationStableCapacity.LoadedJacobianConjugacy

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section
open PhosphorylationSharpness

/-- The full literal state corresponding to one loaded class coordinate. -/
def stateFromLoaded {n : ℕ} (ET FT ST : ℝ)
    (u : CoordinateSpace n) : State n :=
  unChart ET FT ST (ofCoordinateSpace (fromLoadedCoord u))

/-- Exact kinase-complex velocity in the fixed-total loaded chart. -/
theorem loadedFastField_C {n : ℕ} (ET FT ST : ℝ)
    (k : Rates n) (u : CoordinateSpace n) (i : Fin n) :
    (loadedRestrictedField ET FT ST k u).2.1 i =
      k.a i * (stateFromLoaded ET FT ST u).S i.castSucc *
        (stateFromLoaded ET FT ST u).E -
      (k.b i + k.c i) * (stateFromLoaded ET FT ST u).C i := by
  change (field k (stateFromLoaded ET FT ST u)).C i = _
  dsimp [field, kinaseNet]
  ring

/-- Exact phosphatase-complex velocity in the same chart. -/
theorem loadedFastField_D {n : ℕ} (ET FT ST : ℝ)
    (k : Rates n) (u : CoordinateSpace n) (i : Fin n) :
    (loadedRestrictedField ET FT ST k u).2.2 i =
      k.alpha i * (stateFromLoaded ET FT ST u).S i.succ *
        (stateFromLoaded ET FT ST u).F -
      (k.beta i + k.gamma i) * (stateFromLoaded ET FT ST u).D i := by
  change (field k (stateFromLoaded ET FT ST u)).D i = _
  dsimp [field, phosphataseNet]
  ring

end
end PhosphorylationStableCapacity
