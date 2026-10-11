module
public import proofs.PhosphorylationStableCapacity.RelaxationRates
public import proofs.PhosphorylationStableCapacity.LoadedFieldCurrent

@[expose] public section

namespace PhosphorylationStableCapacity

open PhosphorylationSharpness

noncomputable section

/-- In loaded substrate coordinates, relaxation leaves the slow catalytic
field exactly unchanged at every state. -/
theorem relaxRates_loadedLevel_field {n : ℕ}
    (k : Rates n) (x : State n) (j : Fin (n + 1)) (ε : ℝ) :
    loadedLevel (field (relaxRates k ε) x) j =
      loadedLevel (field k x) j := by
  rw [loadedLevel_field_eq_catalytic_flux,
    loadedLevel_field_eq_catalytic_flux]
  rfl

/-- Every kinase-complex velocity is the original complex velocity scaled
by `ε⁻¹`, before restricting to an equilibrium. -/
theorem relaxRates_field_C {n : ℕ}
    (k : Rates n) (x : State n) (i : Fin n)
    {ε : ℝ} (hε : ε ≠ 0) :
    (field (relaxRates k ε) x).C i = (field k x).C i / ε := by
  dsimp [field, kinaseNet, relaxRates]
  field_simp
  ring

/-- The analogous exact scaling holds for every phosphatase-complex
velocity. -/
theorem relaxRates_field_D {n : ℕ}
    (k : Rates n) (x : State n) (i : Fin n)
    {ε : ℝ} (hε : ε ≠ 0) :
    (field (relaxRates k ε) x).D i = (field k x).D i / ε := by
  dsimp [field, phosphataseNet, relaxRates]
  field_simp
  ring

end
end PhosphorylationStableCapacity
