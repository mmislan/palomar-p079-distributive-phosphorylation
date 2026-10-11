module
public import proofs.PhosphorylationStableCapacity.BenchmarkOperationalSemanticTwo
public import proofs.PhosphorylationStableCapacity.OperationalCertifiedModel
public import proofs.PhosphorylationStableCapacity.OperationalSinkOutcome

@[expose] public section

/- Source component: BenchmarkOperationalEnergyTwo -/
namespace PhosphorylationStableCapacity
noncomputable section
open Matrix
open scoped BigOperators

theorem operationalTwo_J_eq_actual_nominal_jacobian :
    operationalTwoJ.realMatrix =
      operationalReactionJacobian operationalTwoIntervalCoordinates
        operationalTwoIntervalScales
        (fun i : Fin 21 => (operationalTwoIntervalNominal (Fin.castAdd 9 i) : ℝ)) 0 := by
  rw [operationalReactionJacobian_at_rational_centre,
    ← operationalTwo_nominal_species_reconstruction_exact,
    ← operationalTwo_rates_eq_independent_nominal_parameters,
    ScaledIntegerMatrix.realMatrix_eq_rational_cast]
  exact congrArg (fun A : Matrix (Fin 9) (Fin 9) ℚ => A.map (Rat.castHom ℝ))
    operationalTwo_nominal_derivative_exact

theorem operationalTwo_Q_eq_actual_nominal_lyapunov_form :
    operationalTwoQ.realMatrix =
      -((operationalReactionJacobian operationalTwoIntervalCoordinates
          operationalTwoIntervalScales
          (fun i : Fin 21 => (operationalTwoIntervalNominal (Fin.castAdd 9 i) : ℝ)) 0).transpose *
            operationalTwoP.realMatrix +
        operationalTwoP.realMatrix *
          operationalReactionJacobian operationalTwoIntervalCoordinates
            operationalTwoIntervalScales
            (fun i : Fin 21 => (operationalTwoIntervalNominal (Fin.castAdd 9 i) : ℝ)) 0) := by
  rw [← operationalTwo_J_eq_actual_nominal_jacobian,
    operationalTwoPLyap_real_identity, neg_neg]

theorem operationalTwo_P_operator_norm_exact :
    ‖matrixSupContinuousMap operationalTwoP.realMatrix‖ =
      (operationalTwoPRowBound : ℝ) := by
  apply matrixSupContinuousMap_norm_eq_row_max _ _
    (by norm_num [operationalTwoPRowBound]) operationalTwoP_absolute_rows
  obtain ⟨i, hi⟩ := operationalTwo_P_row_max_attained
  refine ⟨i, ?_⟩
  rw [ScaledIntegerMatrix.realMatrix_eq_rational_cast]
  change (∑ j : Fin 9, |(operationalTwoP.rationalMatrix i j : ℝ)|) = _
  exact_mod_cast hi

theorem operationalTwo_QInverse_operator_norm_exact :
    ‖matrixSupContinuousMap operationalTwoQInverse.realMatrix‖ =
      (operationalTwoQInverseRowBound : ℝ) := by
  apply matrixSupContinuousMap_norm_eq_row_max _ _
    (by norm_num [operationalTwoQInverseRowBound]) operationalTwoQInverse_absolute_rows
  obtain ⟨i, hi⟩ := operationalTwo_QInverse_row_max_attained
  refine ⟨i, ?_⟩
  rw [ScaledIntegerMatrix.realMatrix_eq_rational_cast]
  change (∑ j : Fin 9, |(operationalTwoQInverse.rationalMatrix i j : ℝ)|) = _
  exact_mod_cast hi

theorem operationalTwo_nominal_lyapunov_data :
    OperationalNominalLyapunovData operationalTwoIntervalCoordinates
      operationalTwoIntervalScales
      (fun i : Fin 21 => operationalTwoIntervalNominal (Fin.castAdd 9 i))
      operationalTwoP.realMatrix operationalTwoQ.realMatrix
      operationalTwoQInverse.realMatrix (operationalTwoDecayMargin : ℝ)
      (489688143626661270927230150387757428988666312583057387523196772556661289010094942204927686144971255286670470601623/19940451679071769213046230667604449464772368013801095203005229248592935834727757199382838188284313600000000000000000 : ℝ) := by
  refine ⟨operationalTwo_Q_eq_actual_nominal_lyapunov_form,
    operationalTwoQ_posDef, operationalTwoQ_real_inverse, ?_,
    Rat.cast_pos.mpr operationalTwo_decay_margin_positive⟩
  rw [operationalTwo_QInverse_operator_norm_exact]
  norm_num [operationalTwoDecayMargin, operationalTwoQInverseRowBound]

theorem operationalTwo_P_printed_lower (v : Fin 9 → ℝ) :
    (1/100 : ℝ)*(∑ i, v i^2) ≤ v ⬝ᵥ (operationalTwoP.realMatrix *ᵥ v) := by
  have hc : (1/100 : ℝ) ≤ 1/(operationalTwoPInverseRowBound : ℝ) := by
    norm_num [operationalTwoPInverseRowBound]
  have hs : 0 ≤ ∑ i, v i^2 := Finset.sum_nonneg (fun i _ => sq_nonneg (v i))
  have hm := mul_le_mul_of_nonneg_right hc hs
  have hbound : (1/100 : ℝ)*(∑ i, v i^2) ≤
      (∑ i, v i^2)/(operationalTwoPInverseRowBound : ℝ) := by
    simpa only [one_div, div_eq_mul_inv, mul_comm, one_mul] using hm
  exact hbound.trans (operationalTwo_P_inverse_coercivity v)

/-- The printed positive decay constant bounds the actual nonlinear
Jacobian at every state and every independent parameter in the same box. -/
theorem operationalTwo_actual_uniform_dissipation
    (θ : Fin 21 → ℝ)
    (hθ : ∀ i : Fin 21,
      |θ i-(operationalTwoIntervalNominal (Fin.castAdd 9 i) : ℝ)| ≤
        (1/671088640000 : ℝ)*(operationalTwoIntervalNominal (Fin.castAdd 9 i) : ℝ))
    (w : Fin 9 → ℝ) (hw : ‖w‖ ≤ (1/16384000 : ℝ)) (v : Fin 9 → ℝ) :
    2*(v ⬝ᵥ (operationalTwoP.realMatrix *ᵥ
      (operationalReactionJacobian operationalTwoIntervalCoordinates
        operationalTwoIntervalScales θ w *ᵥ v))) ≤
      -(operationalTwoDecayMargin : ℝ)*(∑ i, v i^2) := by
  have hC : (Matrix.of operationalTwoIntervalLyapunovCoefficients).map (Rat.castHom ℝ) =
      operationalTwoP.realMatrix *
        operationalWeightedStoichiometry (fun i => (operationalTwoIntervalScales i : ℝ)) := by
    rw [ScaledIntegerMatrix.realMatrix_eq_rational_cast,
      operationalWeightedStoichiometry_eq_rational_cast, ← Matrix.map_mul]
    exact congrArg (fun A : Matrix (Fin 9) (Fin 18) ℚ => A.map (Rat.castHom ℝ))
      operationalTwo_lyapunov_coefficients_exact
  have hJ : operationalTwoJ.realMatrix =
      (operationalRationalStoichiometry operationalTwoIntervalScales *
        operationalRationalDerivative operationalTwoIntervalScales
          operationalTwoIntervalNominalRates operationalTwoIntervalNominalSpecies).map
            (Rat.castHom ℝ) := by
    rw [ScaledIntegerMatrix.realMatrix_eq_rational_cast]
    exact congrArg (fun A : Matrix (Fin 9) (Fin 9) ℚ => A.map (Rat.castHom ℝ))
      operationalTwo_nominal_derivative_exact
  have hinput : ∀ i, (operationalTwoIntervalDomain i).Contains
      (operationalInput θ w i) := by
    rw [operationalTwo_independent_domain_exact]
    exact operationalInput_mem_independent_domain _ _ _ θ w
      (by norm_num only [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]; exact hθ)
      (by norm_num only [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]; exact hw)
  have hmargin : (operationalTwoDecayMargin : ℝ) =
      (1 : ℝ)/(operationalTwoQInverseRowBound : ℝ)-
      (489688143626661270927230150387757428988666312583057387523196772556661289010094942204927686144971255286670470601623/19940451679071769213046230667604449464772368013801095203005229248592935834727757199382838188284313600000000000000000 : ℝ) := by
    norm_num [operationalTwoDecayMargin, operationalTwoQInverseRowBound]
  have h := operational_actual_lyapunov_dissipation
    (Matrix.of operationalTwoIntervalLyapunovCoefficients)
    operationalTwoIntervalCoordinates operationalTwoIntervalScales
    operationalTwoIntervalNominalRates operationalTwoIntervalNominalSpecies
    operationalTwoJ.realMatrix operationalTwoP.realMatrix operationalTwoQ.realMatrix
    operationalTwoP_posDef.isHermitian.isSymm hC hJ operationalTwoPLyap_real_identity
    (1/(operationalTwoQInverseRowBound : ℝ))
    (fun u => by simpa only [one_div, div_eq_mul_inv, mul_comm, one_mul] using
      operationalTwo_Q_inverse_coercivity u)
    operationalTwoIntervalDomain
    (489688143626661270927230150387757428988666312583057387523196772556661289010094942204927686144971255286670470601623/19940451679071769213046230667604449464772368013801095203005229248592935834727757199382838188284313600000000000000000 : ℚ)
    operationalTwoInterval_decay_loss_rows θ w hinput v
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h
  rw [← hmargin] at h
  exact h

end
end PhosphorylationStableCapacity

/- Source component: BenchmarkOperationalPersistenceTwo -/
namespace PhosphorylationStableCapacity
noncomputable section
open Matrix PhosphorylationSharpness
open scoped BigOperators

/-- The second printed operational box contains exactly one positive physical
equilibrium for every admitted independent perturbation of all21 parameters. -/
theorem operationalTwo_positive_equilibrium_persistence
    (θ : Fin 21 → ℝ)
    (hθ : ∀ i : Fin 21,
      |θ i-(operationalTwoIntervalNominal (Fin.castAdd 9 i) : ℝ)| ≤
        (1/671088640000 : ℝ)*
          (operationalTwoIntervalNominal (Fin.castAdd 9 i) : ℝ)) :
    ∃ w : Fin 9 → ℝ, ‖w‖ ≤ (1/16384000 : ℝ)/4 ∧
      (unChart (θ 18) (θ 19) (θ 20)
        (ofCoordinateSpace
          (operationalUnpack (fun i => (operationalTwoIntervalCoordinates i : ℝ))+
            operationalLift (fun i => (operationalTwoIntervalScales i : ℝ)) w))).Positive ∧
      Equilibrium (operationalParameterRates θ)
        (unChart (θ 18) (θ 19) (θ 20)
          (ofCoordinateSpace
            (operationalUnpack (fun i => (operationalTwoIntervalCoordinates i : ℝ))+
              operationalLift (fun i => (operationalTwoIntervalScales i : ℝ)) w))) ∧
      ∀ v : Fin 9 → ℝ, ‖v‖ ≤ (1/16384000 : ℝ) →
        operationalWeightedField (fun i => (operationalTwoIntervalCoordinates i : ℝ))
          (fun i => (operationalTwoIntervalScales i : ℝ)) θ v = 0 → v = w := by
  have hC : (Matrix.of operationalTwoIntervalNewtonCoefficients).map (Rat.castHom ℝ) =
      operationalTwoJInverse.realMatrix *
        operationalWeightedStoichiometry (fun i => (operationalTwoIntervalScales i : ℝ)) := by
    rw [ScaledIntegerMatrix.realMatrix_eq_rational_cast,
      operationalWeightedStoichiometry_eq_rational_cast, ← Matrix.map_mul]
    exact congrArg (fun A : Matrix (Fin 9) (Fin 18) ℚ => A.map (Rat.castHom ℝ))
      operationalTwo_newton_coefficients_exact
  have hJ : operationalTwoJ.realMatrix =
      (operationalRationalStoichiometry operationalTwoIntervalScales *
        operationalRationalDerivative operationalTwoIntervalScales
          operationalTwoIntervalNominalRates operationalTwoIntervalNominalSpecies).map
            (Rat.castHom ℝ) := by
    rw [ScaledIntegerMatrix.realMatrix_eq_rational_cast]
    exact congrArg (fun A : Matrix (Fin 9) (Fin 9) ℚ => A.map (Rat.castHom ℝ))
      operationalTwo_nominal_derivative_exact
  have hbalanced : operationalWeightedStoichiometry
      (fun i => (operationalTwoIntervalScales i : ℝ)) *ᵥ
        (fun a => (operationalNominalFlux operationalTwoIntervalNominalRates
          operationalTwoIntervalNominalSpecies a : ℝ)) = 0 := by
    rw [operationalWeightedStoichiometry_eq_rational_cast]
    ext i
    have h := congrArg (fun v : Fin 9 → ℚ => (v i : ℝ))
      operationalTwo_nominal_flux_balance
    simp only [Pi.zero_apply, Rat.cast_zero] at h
    change (Rat.castHom ℝ) ((operationalRationalStoichiometry operationalTwoIntervalScales *ᵥ
      operationalNominalFlux operationalTwoIntervalNominalRates
        operationalTwoIntervalNominalSpecies) i) = 0 at h
    rw [RingHom.map_mulVec] at h
    simpa only [Function.comp_def, Rat.coe_castHom, Pi.zero_apply] using h
  have hρ : ((1/16384000 : ℚ) : ℝ) = (1/16384000 : ℝ) := by norm_num
  rw [← hρ]
  apply operational_certified_positive_equilibrium
    (Matrix.of operationalTwoIntervalNewtonCoefficients)
    operationalTwoIntervalCoordinates operationalTwoIntervalScales
    operationalTwoIntervalNominalRates operationalTwoIntervalNominalSpecies
    operationalTwoJInverse.realMatrix operationalTwoJ.realMatrix
    (fun i => (operationalTwo_scales_positive i).ne') hC
    operationalTwoJ_real_inverse hJ hbalanced operationalTwoIntervalDomain
    (1/16384000) (3/262144000) (by norm_num) (by norm_num) (by norm_num)
  · exact operationalTwoInterval_contraction_rows
  · exact operationalTwoInterval_centre_shift
  · exact operationalTwoInterval_positive_species
  · intro w hw
    rw [operationalTwo_independent_domain_exact]
    exact operationalInput_mem_independent_domain _ _ _ θ w
      (by norm_num only [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]; exact hθ) hw

end
end PhosphorylationStableCapacity

/- Source component: BenchmarkOperationalReadoutTwo -/
namespace PhosphorylationStableCapacity
noncomputable section

/-- The literal physical readout, including the full printed measurement
error, lies in the second printed interval at every quarter-radius shift. -/
theorem operationalTwo_measured_readout_interval
    (θ : Fin 21 → ℝ) (w : Fin 9 → ℝ) (measurement : ℝ)
    (hw : ‖w‖ ≤ (1/16384000 : ℝ)/4)
    (hmeasurement : |measurement| ≤ (1/1000 : ℝ)) :
    (1439001/20000000 : ℝ) ≤
      operationalPhysicalReadout
        (fun i => (operationalTwoIntervalCoordinates i : ℝ))
        (fun i => (operationalTwoIntervalScales i : ℝ)) θ w+measurement ∧
    operationalPhysicalReadout
        (fun i => (operationalTwoIntervalCoordinates i : ℝ))
        (fun i => (operationalTwoIntervalScales i : ℝ)) θ w+measurement ≤
      (3697503/50000000 : ℝ) := by
  have hcentre : (1/10 : ℝ)*
      ((operationalTwoIntervalCoordinates 2 : ℝ)+
        (operationalTwoIntervalCoordinates 8 : ℝ)) =
          (145088256/1988871157 : ℝ) := by
    norm_num [operationalTwoIntervalCoordinates]
  have hradius : (1/10 : ℝ)*
      ((operationalTwoIntervalScales 2 : ℝ)+
        (operationalTwoIntervalScales 8 : ℝ))*((1/16384000 : ℝ)/4)+
          (1/1000 : ℝ) = (509151582943/509151016192000 : ℝ) := by
    norm_num [operationalTwoIntervalScales]
  have herror := operationalPhysicalReadout_measurement_bound
    (fun i => (operationalTwoIntervalCoordinates i : ℝ))
    (fun i => (operationalTwoIntervalScales i : ℝ))
    (Rat.cast_nonneg.mpr (operationalTwo_scales_positive 2).le)
    (Rat.cast_nonneg.mpr (operationalTwo_scales_positive 8).le)
    θ w (1/16384000) measurement hw hmeasurement
  rw [hcentre, hradius] at herror
  apply measured_readout_mem_certified_interval
    (145088256/1988871157) _ (509151582943/509151016192000)
    (1439001/20000000) (3697503/50000000) herror
  · norm_num
  · norm_num

end
end PhosphorylationStableCapacity

/- Source component: BenchmarkOperationalRecoveryTwo -/
namespace PhosphorylationStableCapacity
noncomputable section
open Matrix PhosphorylationSharpness
open scoped BigOperators

/-- Every physical solution in seconds from the printed inner ball obeys the
printed recovery envelope, under all21 independent parameter perturbations.
The same fixed rational P and the same equilibrium are used throughout. -/
theorem operationalTwo_physical_forward_recovery
    (θ : Fin 21 → ℝ)
    (hθ : ∀ i : Fin 21,
      |θ i-(operationalTwoIntervalNominal (Fin.castAdd 9 i) : ℝ)| ≤
        (1/671088640000 : ℝ)*(operationalTwoIntervalNominal (Fin.castAdd 9 i) : ℝ))
    (equilibrium initial : Fin 9 → ℝ)
    (hshift : ‖equilibrium‖ ≤ (1/16384000 : ℝ)/4)
    (heq : operationalWeightedField
      (fun i => (operationalTwoIntervalCoordinates i : ℝ))
      (fun i => (operationalTwoIntervalScales i : ℝ)) θ equilibrium = 0)
    (hinit : (∑ i, (initial i-equilibrium i)^2) ≤ (1/327680000000 : ℝ)^2) :
    (∃ γ : ℝ → Fin 9 → ℝ,
      IsOperationalPhysicalCurve (fun i => (operationalTwoIntervalCoordinates i : ℝ))
        (fun i => (operationalTwoIntervalScales i : ℝ)) θ initial γ) ∧
    ∀ γ : ℝ → Fin 9 → ℝ,
      IsOperationalPhysicalCurve (fun i => (operationalTwoIntervalCoordinates i : ℝ))
        (fun i => (operationalTwoIntervalScales i : ℝ)) θ initial γ →
      (∀ t : ℝ, 0 ≤ t → ‖γ t‖ < (1/16384000 : ℝ)) ∧
      (∀ t : ℝ, 0 ≤ t → finiteEuclideanLength (γ t-equilibrium) ≤
        ((1/16384000 : ℝ)/2)*Real.exp
          (-((operationalTwoDecayMargin : ℝ)/(2*(operationalTwoPRowBound : ℝ)))*(t/10))) ∧
      (∀ t : ℝ, (32918000 : ℝ) ≤ t →
        finiteEuclideanLength (γ t-equilibrium) < (1/16384000 : ℝ)/20) := by
  have hpositive : ∀ i, 0 < θ i := operational_independent_parameters_positive
    (fun i => operationalTwoIntervalNominal (Fin.castAdd 9 i)) (1/671088640000)
    θ operationalTwo_nominal_parameters_positive (by norm_num)
    (by norm_num only [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]; exact hθ)
  have hspecies (w : Fin 9 → ℝ) (hw : ‖w‖ ≤ (1/16384000 : ℝ)) :
      ∀ i, 0 < operationalSpecies
        (fun j => (operationalTwoIntervalCoordinates j : ℝ))
        (fun j => (operationalTwoIntervalScales j : ℝ)) θ w i := by
    apply operational_actual_species_positive operationalTwoIntervalCoordinates
      operationalTwoIntervalScales operationalTwoIntervalDomain
      operationalTwoInterval_positive_species θ w
    rw [operationalTwo_independent_domain_exact]
    exact operationalInput_mem_independent_domain _ _ _ θ w
      (by norm_num only [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]; exact hθ)
      (by norm_num only [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]; exact hw)
  have hmargin : (operationalTwoPRowBound : ℝ)*(1/327680000000 : ℝ)^2 <
      (1/100 : ℝ)*((1/16384000 : ℝ)/2)^2 := by
    norm_num [operationalTwoPRowBound]
  obtain ⟨⟨β, hβ⟩, hcertificate⟩ := operational_certified_forward_recovery
    operationalTwoIntervalCoordinates operationalTwoIntervalScales
    (fun i => (operationalTwo_scales_positive i).ne') θ hpositive
    operationalTwoP.realMatrix operationalTwoP_posDef.isHermitian.isSymm
    equilibrium initial (1/16384000) (1/327680000000) (1/100)
    (operationalTwoDecayMargin : ℝ) (operationalTwoPRowBound : ℝ)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (Rat.cast_pos.mpr operationalTwo_decay_margin_positive)
    (by norm_num [operationalTwoPRowBound]) hshift heq hspecies
    operationalTwo_P_printed_lower operationalTwo_P_upper
    (operationalTwo_actual_uniform_dissipation θ hθ) hmargin hinit
  refine ⟨⟨fun t => β (t/10), operational_physical_curve_of_model _ _ θ initial β hβ⟩, ?_⟩
  intro γ hγ
  obtain ⟨hstay, henv, htime⟩ := operational_physical_recovery_of_model_certificate
    (fun i => (operationalTwoIntervalCoordinates i : ℝ))
    (fun i => (operationalTwoIntervalScales i : ℝ)) θ initial equilibrium
    (1/16384000) (operationalTwoDecayMargin : ℝ) (operationalTwoPRowBound : ℝ)
    hcertificate γ hγ
  refine ⟨hstay, henv, ?_⟩
  intro t ht
  apply htime t
  have hprinted : (60 : ℝ)*(operationalTwoPRowBound : ℝ)/
      (operationalTwoDecayMargin : ℝ) ≤ 32918000 := by
    norm_num [operationalTwoPRowBound, operationalTwoDecayMargin]
  exact hprinted.trans ht

end
end PhosphorylationStableCapacity

namespace PhosphorylationStableCapacity
noncomputable section
open Matrix PhosphorylationSharpness
open scoped BigOperators

/-- The closed printed ellipsoid is invariant for every solution of the actual
physical equation, even when the initial energy is exactly the boundary value. -/
theorem operationalTwo_physical_closed_ellipsoid
    (θ : Fin 21 → ℝ)
    (hθ : ∀ i : Fin 21,
      |θ i-(operationalTwoIntervalNominal (Fin.castAdd 9 i) : ℝ)| ≤
        (1/671088640000 : ℝ)*(operationalTwoIntervalNominal (Fin.castAdd 9 i) : ℝ))
    (equilibrium initial : Fin 9 → ℝ)
    (hshift : ‖equilibrium‖ ≤ (1/16384000 : ℝ)/4)
    (heq : operationalWeightedField
      (fun i => (operationalTwoIntervalCoordinates i : ℝ))
      (fun i => (operationalTwoIntervalScales i : ℝ)) θ equilibrium = 0)
    (hinit : (initial-equilibrium) ⬝ᵥ
      (operationalTwoP.realMatrix *ᵥ (initial-equilibrium)) ≤
        (1/100 : ℝ)*((1/16384000 : ℝ)/2)^2) :
    (∃ γ : ℝ → Fin 9 → ℝ,
      IsOperationalPhysicalCurve (fun i => (operationalTwoIntervalCoordinates i : ℝ))
        (fun i => (operationalTwoIntervalScales i : ℝ)) θ initial γ) ∧
    ∀ γ : ℝ → Fin 9 → ℝ,
      IsOperationalPhysicalCurve (fun i => (operationalTwoIntervalCoordinates i : ℝ))
        (fun i => (operationalTwoIntervalScales i : ℝ)) θ initial γ →
      (∀ t : ℝ, 0 ≤ t → (γ t-equilibrium) ⬝ᵥ
        (operationalTwoP.realMatrix *ᵥ (γ t-equilibrium)) ≤
          (1/100 : ℝ)*((1/16384000 : ℝ)/2)^2) ∧
      (∀ t : ℝ, 0 ≤ t → ‖γ t‖ < (1/16384000 : ℝ)) ∧
      (∀ t : ℝ, 0 ≤ t → finiteEuclideanLength (γ t-equilibrium) ≤
        ((1/16384000 : ℝ)/2)*Real.exp
          (-((operationalTwoDecayMargin : ℝ)/(2*(operationalTwoPRowBound : ℝ)))*(t/10))) ∧
      (∀ t : ℝ, (32918000 : ℝ) ≤ t →
        finiteEuclideanLength (γ t-equilibrium) < (1/16384000 : ℝ)/20) := by
  have hpositive : ∀ i, 0 < θ i := operational_independent_parameters_positive
    (fun i => operationalTwoIntervalNominal (Fin.castAdd 9 i)) (1/671088640000)
    θ operationalTwo_nominal_parameters_positive (by norm_num)
    (by norm_num only [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]; exact hθ)
  have hsumsq : (∑ i, (initial i-equilibrium i)^2) ≤
      ((1/16384000 : ℝ)/2)^2 := by
    have hlower := operationalTwo_P_printed_lower (initial-equilibrium)
    simp only [Pi.sub_apply] at hlower
    nlinarith [hlower]
  have hdist : ‖initial-equilibrium‖ ≤ (1/16384000 : ℝ)/2 :=
    (sup_norm_le_finiteEuclideanLength (initial-equilibrium)).trans
      (Real.sqrt_le_iff.mpr ⟨by norm_num, hsumsq⟩)
  have hinitial : ‖initial‖ ≤ (1/16384000 : ℝ) := by
    have hi : initial = (initial-equilibrium)+equilibrium := by abel
    rw [hi]
    have hn := norm_add_le (initial-equilibrium) equilibrium
    linarith only [hn, hdist, hshift]
  have hspecies : ∀ i, 0 < operationalSpecies
      (fun j => (operationalTwoIntervalCoordinates j : ℝ))
      (fun j => (operationalTwoIntervalScales j : ℝ)) θ initial i := by
    apply operational_actual_species_positive operationalTwoIntervalCoordinates
      operationalTwoIntervalScales operationalTwoIntervalDomain
      operationalTwoInterval_positive_species θ initial
    rw [operationalTwo_independent_domain_exact]
    exact operationalInput_mem_independent_domain _ _ _ θ initial
      (by norm_num only [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]; exact hθ)
      (by norm_num only [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]; exact hinitial)
  refine ⟨operational_exists_physical_forward_curve _ _
    (fun i => (operationalTwo_scales_positive i).ne') θ hpositive initial hspecies, ?_⟩
  intro γ hγ
  obtain ⟨henergy, hstay, henv, htime⟩ := operational_certified_physical_closed_ellipsoid
    operationalTwoIntervalCoordinates operationalTwoIntervalScales θ
    operationalTwoP.realMatrix operationalTwoP_posDef.isHermitian.isSymm
    equilibrium (1/16384000) (1/100) (operationalTwoDecayMargin : ℝ)
    (operationalTwoPRowBound : ℝ) (by norm_num) (by norm_num)
    (Rat.cast_pos.mpr operationalTwo_decay_margin_positive)
    (by norm_num [operationalTwoPRowBound]) hshift heq
    operationalTwo_P_printed_lower operationalTwo_P_upper
    (operationalTwo_actual_uniform_dissipation θ hθ) initial γ hγ hinit
  refine ⟨henergy, hstay, henv, ?_⟩
  intro t ht
  apply htime t
  have hprinted : (60 : ℝ)*(operationalTwoPRowBound : ℝ)/
      (operationalTwoDecayMargin : ℝ) ≤ 32918000 := by
    norm_num [operationalTwoPRowBound, operationalTwoDecayMargin]
  exact hprinted.trans ht

end
end PhosphorylationStableCapacity
