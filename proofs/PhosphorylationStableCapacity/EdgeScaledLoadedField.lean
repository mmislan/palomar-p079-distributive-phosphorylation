module
public import proofs.PhosphorylationStableCapacity.CoalescedFinalRateRetune
public import proofs.PhosphorylationStableCapacity.LoadedClassChart
public import proofs.PhosphorylationStableCapacity.LoadedFieldCurrent

@[expose] public section

namespace PhosphorylationStableCapacity

open PhosphorylationSharpness

noncomputable section

theorem edgeScaledRates_kinaseNet {n : ℕ} (w : Fin n → ℝ)
    (k : Rates n) (x : State n) (i : Fin n) :
    kinaseNet (edgeScaledRates w k) x i =
      w i * kinaseNet k x i := by
  simp only [kinaseNet, edgeScaledRates]
  ring

theorem edgeScaledRates_phosphataseNet {n : ℕ} (w : Fin n → ℝ)
    (k : Rates n) (x : State n) (i : Fin n) :
    phosphataseNet (edgeScaledRates w k) x i =
      w i * phosphataseNet k x i := by
  simp only [phosphataseNet, edgeScaledRates]
  ring

theorem edgeScaledRates_field_C {n : ℕ} (w : Fin n → ℝ)
    (k : Rates n) (x : State n) (i : Fin n) :
    (field (edgeScaledRates w k) x).C i =
      w i * (field k x).C i := by
  change kinaseNet (edgeScaledRates w k) x i -
    (w i * k.c i) * x.C i =
      w i * (kinaseNet k x i - k.c i * x.C i)
  rw [edgeScaledRates_kinaseNet]
  ring

theorem edgeScaledRates_field_D {n : ℕ} (w : Fin n → ℝ)
    (k : Rates n) (x : State n) (i : Fin n) :
    (field (edgeScaledRates w k) x).D i =
      w i * (field k x).D i := by
  change phosphataseNet (edgeScaledRates w k) x i -
    (w i * k.gamma i) * x.D i =
      w i * (phosphataseNet k x i - k.gamma i * x.D i)
  rw [edgeScaledRates_phosphataseNet]
  ring

/-- The loaded slow field sees a row-weighted catalytic current before
path incidence assembles it into level velocities. -/
theorem edgeScaledRates_loadedLevel_field {n : ℕ} (w : Fin n → ℝ)
    (k : Rates n) (x : State n) (j : Fin (n + 1)) :
    loadedLevel (field (edgeScaledRates w k) x) j =
      ∑ i : Fin n,
        ((if i.succ = j then
          w i * (k.c i * x.C i - k.gamma i * x.D i) else 0) -
         (if i.castSucc = j then
          w i * (k.c i * x.C i - k.gamma i * x.D i) else 0)) := by
  rw [loadedLevel_field_eq_catalytic_flux]
  apply Finset.sum_congr rfl
  intro i _
  simp only [edgeScaledRates]
  split_ifs <;> ring

theorem edgeScaledRates_loadedRestrictedField_C {n : ℕ}
    (ET FT ST : ℝ) (w : Fin n → ℝ) (k : Rates n)
    (u : CoordinateSpace n) (i : Fin n) :
    (loadedRestrictedField ET FT ST (edgeScaledRates w k) u).2.1 i =
      w i * (loadedRestrictedField ET FT ST k u).2.1 i := by
  simpa [loadedRestrictedField, toLoadedCoord, restrictedFieldEuclid,
    restrictedField, toCoordinateSpace, chart] using
    edgeScaledRates_field_C w k
      (unChart ET FT ST (ofCoordinateSpace (fromLoadedCoord u))) i

theorem edgeScaledRates_loadedRestrictedField_D {n : ℕ}
    (ET FT ST : ℝ) (w : Fin n → ℝ) (k : Rates n)
    (u : CoordinateSpace n) (i : Fin n) :
    (loadedRestrictedField ET FT ST (edgeScaledRates w k) u).2.2 i =
      w i * (loadedRestrictedField ET FT ST k u).2.2 i := by
  simpa [loadedRestrictedField, toLoadedCoord, restrictedFieldEuclid,
    restrictedField, toCoordinateSpace, chart] using
    edgeScaledRates_field_D w k
      (unChart ET FT ST (ofCoordinateSpace (fromLoadedCoord u))) i

end
end PhosphorylationStableCapacity
