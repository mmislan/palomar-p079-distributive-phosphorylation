module
public import proofs.PhosphorylationStableCapacity.BenchmarkOperationalIntervalZero
public import proofs.PhosphorylationStableCapacity.BenchmarkOperationalInverseZero
public import proofs.PhosphorylationStableCapacity.BenchmarkOperationalNormZero
public import proofs.PhosphorylationStableCapacity.OperationalCertificateAlgebra

@[expose] public section

namespace PhosphorylationStableCapacity
open Matrix
open scoped BigOperators

set_option maxHeartbeats 2000000

/-- These are semantic equations for the same nominal data and AST coefficient
arrays as the interval certificates, checked with exact kernel arithmetic. -/
theorem operationalZero_independent_domain_exact :
    operationalZeroIntervalDomain = operationalIndependentDomain
      (fun i : Fin 21 => operationalZeroIntervalNominal (Fin.castAdd 9 i))
      (1/671088640000 : ℚ) (1/8192000 : ℚ) := by
  decide +kernel

theorem operationalZero_newton_coefficients_exact :
    operationalZeroIntervalNewtonCoefficients =
      operationalZeroJInverse.rationalMatrix *
        operationalRationalStoichiometry operationalZeroIntervalScales := by
  decide +kernel

theorem operationalZero_lyapunov_coefficients_exact :
    operationalZeroIntervalLyapunovCoefficients =
      operationalZeroP.rationalMatrix *
        operationalRationalStoichiometry operationalZeroIntervalScales := by
  decide +kernel

theorem operationalZero_nominal_derivative_exact :
    operationalZeroJ.rationalMatrix =
      operationalRationalStoichiometry operationalZeroIntervalScales *
        operationalRationalDerivative operationalZeroIntervalScales
          operationalZeroIntervalNominalRates operationalZeroIntervalNominalSpecies := by
  decide +kernel

theorem operationalZero_nominal_flux_balance :
    operationalRationalStoichiometry operationalZeroIntervalScales *ᵥ
      operationalNominalFlux operationalZeroIntervalNominalRates operationalZeroIntervalNominalSpecies = 0 := by
  decide +kernel

theorem operationalZero_nominal_species_reconstruction_exact :
    operationalZeroIntervalNominalSpecies = operationalRationalCentreSpecies operationalZeroIntervalCoordinates
      (fun i : Fin 21 => operationalZeroIntervalNominal (Fin.castAdd 9 i)) := by
  decide +kernel

theorem operationalZero_scales_positive : ∀ i : Fin 9, 0 < operationalZeroIntervalScales i := by
  decide +kernel

theorem operationalZero_scales_eq_nominal_coordinates :
    operationalZeroIntervalScales = operationalZeroIntervalCoordinates := by
  decide +kernel

theorem operationalZero_rates_eq_independent_nominal_parameters :
    operationalZeroIntervalNominalRates = fun a : Fin 18 =>
      operationalZeroIntervalNominal (Fin.castAdd 9 (Fin.castAdd 3 a)) := by
  decide +kernel

theorem operationalZero_nominal_parameters_positive :
    ∀ i : Fin 21, 0 < operationalZeroIntervalNominal (Fin.castAdd 9 i) := by
  decide +kernel

theorem operationalZero_P_row_max_attained :
    ∃ i : Fin 9, (∑ j : Fin 9, |operationalZeroP.rationalMatrix i j|) = operationalZeroPRowBound := by
  decide +kernel

theorem operationalZero_P_integer_symm : operationalZeroP.entries.IsSymm := by
  decide +kernel

theorem operationalZero_QInverse_row_max_attained :
    ∃ i : Fin 9, (∑ j : Fin 9, |operationalZeroQInverse.rationalMatrix i j|) = operationalZeroQInverseRowBound := by
  decide +kernel

theorem operationalZero_decay_margin_exact :
    operationalZeroDecayMargin = 1/operationalZeroQInverseRowBound-(218764808329051461578859664168415574856896977253299942183080347793378744494716931669151270266485111504209/14787547339777033195991071424383892203979741648460352142542874901487227497663485514140876800000000000000000 : ℚ) := by
  decide +kernel

theorem operationalZero_readout_centre_exact :
    (1/10 : ℚ)*(operationalZeroIntervalCoordinates 2+operationalZeroIntervalCoordinates 8) = (566751/167692250 : ℚ) := by
  decide +kernel

theorem operationalZero_readout_radius_exact :
    (1/10 : ℚ)*(operationalZeroIntervalScales 2+operationalZeroIntervalScales 8)*((1/8192000 : ℚ)/4)+(1/1000 : ℚ) =
      (5494940214751/5494939648000000 : ℚ) := by
  decide +kernel

end PhosphorylationStableCapacity
