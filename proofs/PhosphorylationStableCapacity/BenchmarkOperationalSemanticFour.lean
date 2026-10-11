module
public import proofs.PhosphorylationStableCapacity.BenchmarkOperationalIntervalFour
public import proofs.PhosphorylationStableCapacity.BenchmarkOperationalInverseFour
public import proofs.PhosphorylationStableCapacity.BenchmarkOperationalNormFour
public import proofs.PhosphorylationStableCapacity.OperationalCertificateAlgebra

@[expose] public section

namespace PhosphorylationStableCapacity
open Matrix
open scoped BigOperators

set_option maxHeartbeats 2000000

/-- These are semantic equations for the same nominal data and AST coefficient
arrays as the interval certificates, checked with exact kernel arithmetic. -/
theorem operationalFour_independent_domain_exact :
    operationalFourIntervalDomain = operationalIndependentDomain
      (fun i : Fin 21 => operationalFourIntervalNominal (Fin.castAdd 9 i))
      (1/671088640000 : ℚ) (1/2048000 : ℚ) := by
  decide +kernel

theorem operationalFour_newton_coefficients_exact :
    operationalFourIntervalNewtonCoefficients =
      operationalFourJInverse.rationalMatrix *
        operationalRationalStoichiometry operationalFourIntervalScales := by
  decide +kernel

theorem operationalFour_lyapunov_coefficients_exact :
    operationalFourIntervalLyapunovCoefficients =
      operationalFourP.rationalMatrix *
        operationalRationalStoichiometry operationalFourIntervalScales := by
  decide +kernel

theorem operationalFour_nominal_derivative_exact :
    operationalFourJ.rationalMatrix =
      operationalRationalStoichiometry operationalFourIntervalScales *
        operationalRationalDerivative operationalFourIntervalScales
          operationalFourIntervalNominalRates operationalFourIntervalNominalSpecies := by
  decide +kernel

theorem operationalFour_nominal_flux_balance :
    operationalRationalStoichiometry operationalFourIntervalScales *ᵥ
      operationalNominalFlux operationalFourIntervalNominalRates operationalFourIntervalNominalSpecies = 0 := by
  decide +kernel

theorem operationalFour_nominal_species_reconstruction_exact :
    operationalFourIntervalNominalSpecies = operationalRationalCentreSpecies operationalFourIntervalCoordinates
      (fun i : Fin 21 => operationalFourIntervalNominal (Fin.castAdd 9 i)) := by
  decide +kernel

theorem operationalFour_scales_positive : ∀ i : Fin 9, 0 < operationalFourIntervalScales i := by
  decide +kernel

theorem operationalFour_scales_eq_nominal_coordinates :
    operationalFourIntervalScales = operationalFourIntervalCoordinates := by
  decide +kernel

theorem operationalFour_rates_eq_independent_nominal_parameters :
    operationalFourIntervalNominalRates = fun a : Fin 18 =>
      operationalFourIntervalNominal (Fin.castAdd 9 (Fin.castAdd 3 a)) := by
  decide +kernel

theorem operationalFour_nominal_parameters_positive :
    ∀ i : Fin 21, 0 < operationalFourIntervalNominal (Fin.castAdd 9 i) := by
  decide +kernel

theorem operationalFour_P_row_max_attained :
    ∃ i : Fin 9, (∑ j : Fin 9, |operationalFourP.rationalMatrix i j|) = operationalFourPRowBound := by
  decide +kernel

theorem operationalFour_P_integer_symm : operationalFourP.entries.IsSymm := by
  decide +kernel

theorem operationalFour_QInverse_row_max_attained :
    ∃ i : Fin 9, (∑ j : Fin 9, |operationalFourQInverse.rationalMatrix i j|) = operationalFourQInverseRowBound := by
  decide +kernel

theorem operationalFour_decay_margin_exact :
    operationalFourDecayMargin = 1/operationalFourQInverseRowBound-(4599501469907009612464002751315450826328711932522883905127728262836218206833047661497370341089714584554295941/245291609798590978623041458588212757858564254475582332674050107111671862729092679484239878553600000000000000000 : ℚ) := by
  decide +kernel

theorem operationalFour_readout_centre_exact :
    (1/10 : ℚ)*(operationalFourIntervalCoordinates 2+operationalFourIntervalCoordinates 8) = (11901771/55060850 : ℚ) := by
  decide +kernel

theorem operationalFour_readout_radius_exact :
    (1/10 : ℚ)*(operationalFourIntervalScales 2+operationalFourIntervalScales 8)*((1/2048000 : ℚ)/4)+(1/1000 : ℚ) =
      (451070384971/451058483200000 : ℚ) := by
  decide +kernel

end PhosphorylationStableCapacity
