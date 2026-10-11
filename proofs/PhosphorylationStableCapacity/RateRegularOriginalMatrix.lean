module
public import proofs.PhosphorylationStableCapacity.RateCancellationSard
public import proofs.PhosphorylationStableCapacity.SplitRelaxDeterminant
public import proofs.PhosphorylationStableCapacity.LoadedStateChartBridge

@[expose] public section

namespace PhosphorylationStableCapacity

open PhosphorylationSharpness

noncomputable section

/-- The matrix used in the literal class-Jacobian calculations has
exactly the determinant of the loaded Fréchet derivative. -/
theorem loadedJacobianMatrix_det_eq_fderiv {n : ℕ}
    (ET FT ST : ℝ) (k : Rates n) (u : CoordinateSpace n) :
    (loadedJacobianMatrix ET FT ST k u).det =
      (fderiv ℝ (loadedRestrictedField ET FT ST k) u).det := by
  exact LinearMap.det_toMatrix (coordinateBasis n)
    (fderiv ℝ (loadedRestrictedField ET FT ST k) u).toLinearMap

/-- The standard manuscript class-Jacobian matrix has the same
determinant as the loaded Fréchet derivative at corresponding states. -/
theorem restrictedJacobianMatrix_det_eq_loaded_fderiv {n : ℕ}
    (ET FT ST : ℝ) (k : Rates n) (u : CoordinateSpace n) :
    (restrictedJacobianMatrix ET FT ST k (fromLoadedCoord u)).det =
      (fderiv ℝ (loadedRestrictedField ET FT ST k) u).det := by
  rw [restrictedJacobianMatrix_det_eq_loaded,
    loadedJacobianMatrix_det_eq_fderiv]

/-- For every positive base rate list and every parameter
neighborhood, a positive perturbation makes the literal manuscript
class-Jacobian matrix nonsingular at every positive equilibrium. -/
theorem nearby_positive_rates_original_matrix_regular {n : ℕ}
    (ET FT ST : ℝ) (k : Rates n) (hk : k.Positive)
    {U : Set (CoordinateSpace n)} (hU : IsOpen U)
    (hzero : (0 : CoordinateSpace n) ∈ U) :
    ∃ v ∈ U, (ratesAdd k (selectedRates v)).Positive ∧
      ∀ u : CoordinateSpace n,
        (stateFromLoaded ET FT ST u).Positive →
        restrictedFieldEuclid ET FT ST
          (ratesAdd k (selectedRates v)) (fromLoadedCoord u) = 0 →
        (restrictedJacobianMatrix ET FT ST
          (ratesAdd k (selectedRates v)) (fromLoadedCoord u)).det ≠ 0 := by
  obtain ⟨v, hvU, hvpos, hvregular⟩ :=
    nearby_positive_rates_all_equilibria_regular ET FT ST k hk hU hzero
  refine ⟨v, hvU, hvpos, ?_⟩
  intro u hx heq
  have hloaded : loadedRestrictedField ET FT ST
      (ratesAdd k (selectedRates v)) u = 0 := by
    change toLoadedCoord
      (restrictedFieldEuclid ET FT ST
        (ratesAdd k (selectedRates v)) (fromLoadedCoord u)) = 0
    rw [heq]
    exact map_zero (loadedCoordLinear n)
  rw [restrictedJacobianMatrix_det_eq_loaded_fderiv]
  exact hvregular u hx hloaded

/-- The same regularity assertion quantified directly over literal
positive equilibria in the prescribed stoichiometric class. -/
theorem nearby_positive_rates_literal_equilibria_regular {n : ℕ}
    (ET FT ST : ℝ) (k : Rates n) (hk : k.Positive)
    {U : Set (CoordinateSpace n)} (hU : IsOpen U)
    (hzero : (0 : CoordinateSpace n) ∈ U) :
    ∃ v ∈ U, (ratesAdd k (selectedRates v)).Positive ∧
      ∀ x : State n,
        x.Positive → InClass ET FT ST x →
        Equilibrium (ratesAdd k (selectedRates v)) x →
        (restrictedJacobianMatrix ET FT ST
          (ratesAdd k (selectedRates v))
          (toCoordinateSpace (chart x))).det ≠ 0 := by
  obtain ⟨v, hvU, hvpos, hvregular⟩ :=
    nearby_positive_rates_original_matrix_regular ET FT ST k hk hU hzero
  refine ⟨v, hvU, hvpos, ?_⟩
  intro x hx hxclass hxeq
  let u := loadedCoordOfState x
  have hstate : stateFromLoaded ET FT ST u = x :=
    stateFromLoaded_loadedCoordOfState ET FT ST x hxclass
  have hcoord : fromLoadedCoord u = toCoordinateSpace (chart x) := by
    exact from_toLoadedCoord _
  rw [← hcoord]
  apply hvregular u
  · rw [hstate]
    exact hx
  · apply (restrictedFieldEuclid_eq_zero_iff ET FT ST
      (ratesAdd k (selectedRates v)) (fromLoadedCoord u)).2
    change Equilibrium (ratesAdd k (selectedRates v))
      (stateFromLoaded ET FT ST u)
    rw [hstate]
    exact hxeq

end
end PhosphorylationStableCapacity
