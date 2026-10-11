module
public import proofs.PhosphorylationStableCapacity.BenchmarkOperationalIntervalTwo
public import proofs.PhosphorylationStableCapacity.BenchmarkOperationalInverseTwo
public import proofs.PhosphorylationStableCapacity.BenchmarkOperationalNormTwo
public import proofs.PhosphorylationStableCapacity.OperationalCertificateAlgebra

@[expose] public section

namespace PhosphorylationStableCapacity
open Matrix
open scoped BigOperators

set_option maxHeartbeats 2000000

/-- These are semantic equations for the same nominal data and AST coefficient
arrays as the interval certificates, checked with exact kernel arithmetic. -/
theorem operationalTwo_independent_domain_exact :
    operationalTwoIntervalDomain = operationalIndependentDomain
      (fun i : Fin 21 => operationalTwoIntervalNominal (Fin.castAdd 9 i))
      (1/671088640000 : ℚ) (1/16384000 : ℚ) := by
  decide +kernel

theorem operationalTwo_newton_coefficients_exact :
    operationalTwoIntervalNewtonCoefficients =
      operationalTwoJInverse.rationalMatrix *
        operationalRationalStoichiometry operationalTwoIntervalScales := by
  decide +kernel

theorem operationalTwo_lyapunov_coefficients_exact :
    operationalTwoIntervalLyapunovCoefficients =
      operationalTwoP.rationalMatrix *
        operationalRationalStoichiometry operationalTwoIntervalScales := by
  decide +kernel

theorem operationalTwo_nominal_derivative_exact :
    operationalTwoJ.rationalMatrix =
      operationalRationalStoichiometry operationalTwoIntervalScales *
        operationalRationalDerivative operationalTwoIntervalScales
          operationalTwoIntervalNominalRates operationalTwoIntervalNominalSpecies := by
  decide +kernel

theorem operationalTwo_nominal_flux_balance :
    operationalRationalStoichiometry operationalTwoIntervalScales *ᵥ
      operationalNominalFlux operationalTwoIntervalNominalRates operationalTwoIntervalNominalSpecies = 0 := by
  decide +kernel

theorem operationalTwo_nominal_species_reconstruction_exact :
    operationalTwoIntervalNominalSpecies = operationalRationalCentreSpecies operationalTwoIntervalCoordinates
      (fun i : Fin 21 => operationalTwoIntervalNominal (Fin.castAdd 9 i)) := by
  decide +kernel

theorem operationalTwo_scales_positive : ∀ i : Fin 9, 0 < operationalTwoIntervalScales i := by
  decide +kernel

theorem operationalTwo_scales_eq_nominal_coordinates :
    operationalTwoIntervalScales = operationalTwoIntervalCoordinates := by
  decide +kernel

theorem operationalTwo_rates_eq_independent_nominal_parameters :
    operationalTwoIntervalNominalRates = fun a : Fin 18 =>
      operationalTwoIntervalNominal (Fin.castAdd 9 (Fin.castAdd 3 a)) := by
  decide +kernel

theorem operationalTwo_nominal_parameters_positive :
    ∀ i : Fin 21, 0 < operationalTwoIntervalNominal (Fin.castAdd 9 i) := by
  decide +kernel

theorem operationalTwo_P_row_max_attained :
    ∃ i : Fin 9, (∑ j : Fin 9, |operationalTwoP.rationalMatrix i j|) = operationalTwoPRowBound := by
  decide +kernel

theorem operationalTwo_P_integer_symm : operationalTwoP.entries.IsSymm := by
  decide +kernel

theorem operationalTwo_QInverse_row_max_attained :
    ∃ i : Fin 9, (∑ j : Fin 9, |operationalTwoQInverse.rationalMatrix i j|) = operationalTwoQInverseRowBound := by
  decide +kernel

theorem operationalTwo_decay_margin_exact :
    operationalTwoDecayMargin = 1/operationalTwoQInverseRowBound-(489688143626661270927230150387757428988666312583057387523196772556661289010094942204927686144971255286670470601623/19940451679071769213046230667604449464772368013801095203005229248592935834727757199382838188284313600000000000000000 : ℚ) := by
  decide +kernel

theorem operationalTwo_readout_centre_exact :
    (1/10 : ℚ)*(operationalTwoIntervalCoordinates 2+operationalTwoIntervalCoordinates 8) = (145088256/1988871157 : ℚ) := by
  decide +kernel

theorem operationalTwo_readout_radius_exact :
    (1/10 : ℚ)*(operationalTwoIntervalScales 2+operationalTwoIntervalScales 8)*((1/16384000 : ℚ)/4)+(1/1000 : ℚ) =
      (509151582943/509151016192000 : ℚ) := by
  decide +kernel

end PhosphorylationStableCapacity
