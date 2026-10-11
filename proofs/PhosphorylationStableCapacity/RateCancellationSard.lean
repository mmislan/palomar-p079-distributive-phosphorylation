module
public import proofs.PhosphorylationStableCapacity.RateCancellationCriticalIff
public import proofs.PhosphorylationStableCapacity.RateSelectedPositiveNeighborhood
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis

@[expose] public section

namespace PhosphorylationStableCapacity

open PhosphorylationSharpness MeasureTheory

noncomputable section

/-- Positive states where the cancellation map has a singular derivative. -/
def cancellationCriticalSet {n : ℕ} (ET FT ST : ℝ) (k : Rates n) :
    Set (CoordinateSpace n) :=
  {u | (stateFromLoaded ET FT ST u).Positive ∧
    (fderiv ℝ (cancellationParameter ET FT ST k) u).det = 0}

/-- Fixed-dimension Sard makes the critical parameter values negligible. -/
theorem cancellationCriticalValues_null {n : ℕ}
    (ET FT ST : ℝ) (k : Rates n) :
    (Module.Free.chooseBasis ℝ (CoordinateSpace n)).addHaar
      (cancellationParameter ET FT ST k ''
      cancellationCriticalSet ET FT ST k) = 0 := by
  apply addHaar_image_eq_zero_of_det_fderivWithin_eq_zero
    (μ := (Module.Free.chooseBasis ℝ (CoordinateSpace n)).addHaar)
    (f' := fun u => fderiv ℝ (cancellationParameter ET FT ST k) u)
  · intro u hu
    exact (differentiableAt_cancellationParameter ET FT ST k u hu.1).hasFDerivAt.hasFDerivWithinAt
  · intro u hu
    exact hu.2

/-- Parameters outside the critical image are dense. -/
theorem cancellationRegularParameters_dense {n : ℕ}
    (ET FT ST : ℝ) (k : Rates n) :
    Dense (cancellationParameter ET FT ST k ''
      cancellationCriticalSet ET FT ST k)ᶜ := by
  exact interior_eq_empty_iff_dense_compl.mp
    (Measure.interior_eq_empty_of_null
      (μ := (Module.Free.chooseBasis ℝ (CoordinateSpace n)).addHaar)
      (cancellationCriticalValues_null ET FT ST k))

/-- Every positive equilibrium at a regular selected-rate parameter
has an invertible class Jacobian. -/
theorem selectedParameter_regular_jacobian {n : ℕ}
    (ET FT ST : ℝ) (k : Rates n) (v u : CoordinateSpace n)
    (hv : v ∈ (cancellationParameter ET FT ST k ''
      cancellationCriticalSet ET FT ST k)ᶜ)
    (hx : (stateFromLoaded ET FT ST u).Positive)
    (hzero : loadedRestrictedField ET FT ST
      (ratesAdd k (selectedRates v)) u = 0) :
    (fderiv ℝ
      (loadedRestrictedField ET FT ST (ratesAdd k (selectedRates v))) u).det ≠ 0 := by
  intro hsing
  have hcrit : u ∈ cancellationCriticalSet ET FT ST k :=
    ⟨hx, (cancellationParameter_critical_iff_jacobian_singular
      ET FT ST k u v hx hzero).2 hsing⟩
  have hgraph : v = cancellationParameter ET FT ST k u :=
    (loadedField_zero_iff_parameter_eq_cancellation ET FT ST k u v hx).1 hzero
  exact hv (hgraph.symm ▸ Set.mem_image_of_mem _ hcrit)

/-- Arbitrarily close selected-rate perturbations preserve literal rate
positivity and make every positive equilibrium regular. -/
theorem nearby_positive_rates_all_equilibria_regular {n : ℕ}
    (ET FT ST : ℝ) (k : Rates n) (hk : k.Positive)
    {U : Set (CoordinateSpace n)} (hU : IsOpen U)
    (hzero : (0 : CoordinateSpace n) ∈ U) :
    ∃ v ∈ U, (ratesAdd k (selectedRates v)).Positive ∧
      ∀ u : CoordinateSpace n,
        (stateFromLoaded ET FT ST u).Positive →
        loadedRestrictedField ET FT ST
          (ratesAdd k (selectedRates v)) u = 0 →
        (fderiv ℝ
          (loadedRestrictedField ET FT ST
            (ratesAdd k (selectedRates v))) u).det ≠ 0 := by
  obtain ⟨V, hVopen, hVzero, hVpositive⟩ :=
    selectedRates_positive_neighborhood k hk
  obtain ⟨v, hvreg, hvUV⟩ :=
    (cancellationRegularParameters_dense ET FT ST k).exists_mem_open
      (hU.inter hVopen) ⟨0, hzero, hVzero⟩
  exact ⟨v, hvUV.1, hVpositive v hvUV.2,
    fun u hx heq => selectedParameter_regular_jacobian
      ET FT ST k v u hvreg hx heq⟩

end
end PhosphorylationStableCapacity
