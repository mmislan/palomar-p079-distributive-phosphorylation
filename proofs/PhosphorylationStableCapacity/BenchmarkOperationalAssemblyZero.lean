module
public import proofs.PhosphorylationStableCapacity.BenchmarkOperationalSemanticZero
public import proofs.PhosphorylationStableCapacity.OperationalCertifiedModel
public import proofs.PhosphorylationStableCapacity.OperationalSinkOutcome

@[expose] public section

/- Source component: BenchmarkOperationalEnergyZero -/
namespace PhosphorylationStableCapacity
noncomputable section
open Matrix
open scoped BigOperators

theorem operationalZero_J_eq_actual_nominal_jacobian :
    operationalZeroJ.realMatrix =
      operationalReactionJacobian operationalZeroIntervalCoordinates
        operationalZeroIntervalScales
        (fun i : Fin 21 => (operationalZeroIntervalNominal (Fin.castAdd 9 i) : ℝ)) 0 := by
  rw [operationalReactionJacobian_at_rational_centre,
    ← operationalZero_nominal_species_reconstruction_exact,
    ← operationalZero_rates_eq_independent_nominal_parameters,
    ScaledIntegerMatrix.realMatrix_eq_rational_cast]
  exact congrArg (fun A : Matrix (Fin 9) (Fin 9) ℚ => A.map (Rat.castHom ℝ))
    operationalZero_nominal_derivative_exact

theorem operationalZero_Q_eq_actual_nominal_lyapunov_form :
    operationalZeroQ.realMatrix =
      -((operationalReactionJacobian operationalZeroIntervalCoordinates
          operationalZeroIntervalScales
          (fun i : Fin 21 => (operationalZeroIntervalNominal (Fin.castAdd 9 i) : ℝ)) 0).transpose *
            operationalZeroP.realMatrix +
        operationalZeroP.realMatrix *
          operationalReactionJacobian operationalZeroIntervalCoordinates
            operationalZeroIntervalScales
            (fun i : Fin 21 => (operationalZeroIntervalNominal (Fin.castAdd 9 i) : ℝ)) 0) := by
  rw [← operationalZero_J_eq_actual_nominal_jacobian,
    operationalZeroPLyap_real_identity, neg_neg]

theorem operationalZero_P_operator_norm_exact :
    ‖matrixSupContinuousMap operationalZeroP.realMatrix‖ =
      (operationalZeroPRowBound : ℝ) := by
  apply matrixSupContinuousMap_norm_eq_row_max _ _
    (by norm_num [operationalZeroPRowBound]) operationalZeroP_absolute_rows
  obtain ⟨i, hi⟩ := operationalZero_P_row_max_attained
  refine ⟨i, ?_⟩
  rw [ScaledIntegerMatrix.realMatrix_eq_rational_cast]
  change (∑ j : Fin 9, |(operationalZeroP.rationalMatrix i j : ℝ)|) = _
  exact_mod_cast hi

theorem operationalZero_QInverse_operator_norm_exact :
    ‖matrixSupContinuousMap operationalZeroQInverse.realMatrix‖ =
      (operationalZeroQInverseRowBound : ℝ) := by
  apply matrixSupContinuousMap_norm_eq_row_max _ _
    (by norm_num [operationalZeroQInverseRowBound]) operationalZeroQInverse_absolute_rows
  obtain ⟨i, hi⟩ := operationalZero_QInverse_row_max_attained
  refine ⟨i, ?_⟩
  rw [ScaledIntegerMatrix.realMatrix_eq_rational_cast]
  change (∑ j : Fin 9, |(operationalZeroQInverse.rationalMatrix i j : ℝ)|) = _
  exact_mod_cast hi

theorem operationalZero_nominal_lyapunov_data :
    OperationalNominalLyapunovData operationalZeroIntervalCoordinates
      operationalZeroIntervalScales
      (fun i : Fin 21 => operationalZeroIntervalNominal (Fin.castAdd 9 i))
      operationalZeroP.realMatrix operationalZeroQ.realMatrix
      operationalZeroQInverse.realMatrix (operationalZeroDecayMargin : ℝ)
      (218764808329051461578859664168415574856896977253299942183080347793378744494716931669151270266485111504209/14787547339777033195991071424383892203979741648460352142542874901487227497663485514140876800000000000000000 : ℝ) := by
  refine ⟨operationalZero_Q_eq_actual_nominal_lyapunov_form,
    operationalZeroQ_posDef, operationalZeroQ_real_inverse, ?_,
    Rat.cast_pos.mpr operationalZero_decay_margin_positive⟩
  rw [operationalZero_QInverse_operator_norm_exact]
  norm_num [operationalZeroDecayMargin, operationalZeroQInverseRowBound]

theorem operationalZero_P_printed_lower (v : Fin 9 → ℝ) :
    (1/100 : ℝ)*(∑ i, v i^2) ≤ v ⬝ᵥ (operationalZeroP.realMatrix *ᵥ v) := by
  have hc : (1/100 : ℝ) ≤ 1/(operationalZeroPInverseRowBound : ℝ) := by
    norm_num [operationalZeroPInverseRowBound]
  have hs : 0 ≤ ∑ i, v i^2 := Finset.sum_nonneg (fun i _ => sq_nonneg (v i))
  have hm := mul_le_mul_of_nonneg_right hc hs
  have hbound : (1/100 : ℝ)*(∑ i, v i^2) ≤
      (∑ i, v i^2)/(operationalZeroPInverseRowBound : ℝ) := by
    simpa only [one_div, div_eq_mul_inv, mul_comm, one_mul] using hm
  exact hbound.trans (operationalZero_P_inverse_coercivity v)

/-- The printed positive decay constant bounds the actual nonlinear
Jacobian at every state and every independent parameter in the same box. -/
theorem operationalZero_actual_uniform_dissipation
    (θ : Fin 21 → ℝ)
    (hθ : ∀ i : Fin 21,
      |θ i-(operationalZeroIntervalNominal (Fin.castAdd 9 i) : ℝ)| ≤
        (1/671088640000 : ℝ)*(operationalZeroIntervalNominal (Fin.castAdd 9 i) : ℝ))
    (w : Fin 9 → ℝ) (hw : ‖w‖ ≤ (1/8192000 : ℝ)) (v : Fin 9 → ℝ) :
    2*(v ⬝ᵥ (operationalZeroP.realMatrix *ᵥ
      (operationalReactionJacobian operationalZeroIntervalCoordinates
        operationalZeroIntervalScales θ w *ᵥ v))) ≤
      -(operationalZeroDecayMargin : ℝ)*(∑ i, v i^2) := by
  have hC : (Matrix.of operationalZeroIntervalLyapunovCoefficients).map (Rat.castHom ℝ) =
      operationalZeroP.realMatrix *
        operationalWeightedStoichiometry (fun i => (operationalZeroIntervalScales i : ℝ)) := by
    rw [ScaledIntegerMatrix.realMatrix_eq_rational_cast,
      operationalWeightedStoichiometry_eq_rational_cast, ← Matrix.map_mul]
    exact congrArg (fun A : Matrix (Fin 9) (Fin 18) ℚ => A.map (Rat.castHom ℝ))
      operationalZero_lyapunov_coefficients_exact
  have hJ : operationalZeroJ.realMatrix =
      (operationalRationalStoichiometry operationalZeroIntervalScales *
        operationalRationalDerivative operationalZeroIntervalScales
          operationalZeroIntervalNominalRates operationalZeroIntervalNominalSpecies).map
            (Rat.castHom ℝ) := by
    rw [ScaledIntegerMatrix.realMatrix_eq_rational_cast]
    exact congrArg (fun A : Matrix (Fin 9) (Fin 9) ℚ => A.map (Rat.castHom ℝ))
      operationalZero_nominal_derivative_exact
  have hinput : ∀ i, (operationalZeroIntervalDomain i).Contains
      (operationalInput θ w i) := by
    rw [operationalZero_independent_domain_exact]
    exact operationalInput_mem_independent_domain _ _ _ θ w
      (by norm_num only [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]; exact hθ)
      (by norm_num only [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]; exact hw)
  have hmargin : (operationalZeroDecayMargin : ℝ) =
      (1 : ℝ)/(operationalZeroQInverseRowBound : ℝ)-
      (218764808329051461578859664168415574856896977253299942183080347793378744494716931669151270266485111504209/14787547339777033195991071424383892203979741648460352142542874901487227497663485514140876800000000000000000 : ℝ) := by
    norm_num [operationalZeroDecayMargin, operationalZeroQInverseRowBound]
  have h := operational_actual_lyapunov_dissipation
    (Matrix.of operationalZeroIntervalLyapunovCoefficients)
    operationalZeroIntervalCoordinates operationalZeroIntervalScales
    operationalZeroIntervalNominalRates operationalZeroIntervalNominalSpecies
    operationalZeroJ.realMatrix operationalZeroP.realMatrix operationalZeroQ.realMatrix
    operationalZeroP_posDef.isHermitian.isSymm hC hJ operationalZeroPLyap_real_identity
    (1/(operationalZeroQInverseRowBound : ℝ))
    (fun u => by simpa only [one_div, div_eq_mul_inv, mul_comm, one_mul] using
      operationalZero_Q_inverse_coercivity u)
    operationalZeroIntervalDomain
    (218764808329051461578859664168415574856896977253299942183080347793378744494716931669151270266485111504209/14787547339777033195991071424383892203979741648460352142542874901487227497663485514140876800000000000000000 : ℚ)
    operationalZeroInterval_decay_loss_rows θ w hinput v
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h
  rw [← hmargin] at h
  exact h

end
end PhosphorylationStableCapacity

/- Source component: BenchmarkOperationalPersistenceZero -/
namespace PhosphorylationStableCapacity
noncomputable section
open Matrix PhosphorylationSharpness
open scoped BigOperators

/-- The first printed operational box contains exactly one positive physical
equilibrium for every admitted independent perturbation of all21 parameters. -/
theorem operationalZero_positive_equilibrium_persistence
    (θ : Fin 21 → ℝ)
    (hθ : ∀ i : Fin 21,
      |θ i-(operationalZeroIntervalNominal (Fin.castAdd 9 i) : ℝ)| ≤
        (1/671088640000 : ℝ)*
          (operationalZeroIntervalNominal (Fin.castAdd 9 i) : ℝ)) :
    ∃ w : Fin 9 → ℝ, ‖w‖ ≤ (1/8192000 : ℝ)/4 ∧
      (unChart (θ 18) (θ 19) (θ 20)
        (ofCoordinateSpace
          (operationalUnpack (fun i => (operationalZeroIntervalCoordinates i : ℝ))+
            operationalLift (fun i => (operationalZeroIntervalScales i : ℝ)) w))).Positive ∧
      Equilibrium (operationalParameterRates θ)
        (unChart (θ 18) (θ 19) (θ 20)
          (ofCoordinateSpace
            (operationalUnpack (fun i => (operationalZeroIntervalCoordinates i : ℝ))+
              operationalLift (fun i => (operationalZeroIntervalScales i : ℝ)) w))) ∧
      ∀ v : Fin 9 → ℝ, ‖v‖ ≤ (1/8192000 : ℝ) →
        operationalWeightedField (fun i => (operationalZeroIntervalCoordinates i : ℝ))
          (fun i => (operationalZeroIntervalScales i : ℝ)) θ v = 0 → v = w := by
  have hC : (Matrix.of operationalZeroIntervalNewtonCoefficients).map (Rat.castHom ℝ) =
      operationalZeroJInverse.realMatrix *
        operationalWeightedStoichiometry (fun i => (operationalZeroIntervalScales i : ℝ)) := by
    rw [ScaledIntegerMatrix.realMatrix_eq_rational_cast,
      operationalWeightedStoichiometry_eq_rational_cast, ← Matrix.map_mul]
    exact congrArg (fun A : Matrix (Fin 9) (Fin 18) ℚ => A.map (Rat.castHom ℝ))
      operationalZero_newton_coefficients_exact
  have hJ : operationalZeroJ.realMatrix =
      (operationalRationalStoichiometry operationalZeroIntervalScales *
        operationalRationalDerivative operationalZeroIntervalScales
          operationalZeroIntervalNominalRates operationalZeroIntervalNominalSpecies).map
            (Rat.castHom ℝ) := by
    rw [ScaledIntegerMatrix.realMatrix_eq_rational_cast]
    exact congrArg (fun A : Matrix (Fin 9) (Fin 9) ℚ => A.map (Rat.castHom ℝ))
      operationalZero_nominal_derivative_exact
  have hbalanced : operationalWeightedStoichiometry
      (fun i => (operationalZeroIntervalScales i : ℝ)) *ᵥ
        (fun a => (operationalNominalFlux operationalZeroIntervalNominalRates
          operationalZeroIntervalNominalSpecies a : ℝ)) = 0 := by
    rw [operationalWeightedStoichiometry_eq_rational_cast]
    ext i
    have h := congrArg (fun v : Fin 9 → ℚ => (v i : ℝ))
      operationalZero_nominal_flux_balance
    simp only [Pi.zero_apply, Rat.cast_zero] at h
    change (Rat.castHom ℝ) ((operationalRationalStoichiometry operationalZeroIntervalScales *ᵥ
      operationalNominalFlux operationalZeroIntervalNominalRates
        operationalZeroIntervalNominalSpecies) i) = 0 at h
    rw [RingHom.map_mulVec] at h
    simpa only [Function.comp_def, Rat.coe_castHom, Pi.zero_apply] using h
  have hρ : ((1/8192000 : ℚ) : ℝ) = (1/8192000 : ℝ) := by norm_num
  rw [← hρ]
  apply operational_certified_positive_equilibrium
    (Matrix.of operationalZeroIntervalNewtonCoefficients)
    operationalZeroIntervalCoordinates operationalZeroIntervalScales
    operationalZeroIntervalNominalRates operationalZeroIntervalNominalSpecies
    operationalZeroJInverse.realMatrix operationalZeroJ.realMatrix
    (fun i => (operationalZero_scales_positive i).ne') hC
    operationalZeroJ_real_inverse hJ hbalanced operationalZeroIntervalDomain
    (1/8192000) (3/131072000) (by norm_num) (by norm_num) (by norm_num)
  · exact operationalZeroInterval_contraction_rows
  · exact operationalZeroInterval_centre_shift
  · exact operationalZeroInterval_positive_species
  · intro w hw
    rw [operationalZero_independent_domain_exact]
    exact operationalInput_mem_independent_domain _ _ _ θ w
      (by norm_num only [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]; exact hθ) hw

end
end PhosphorylationStableCapacity

/- Source component: BenchmarkOperationalReadoutZero -/
namespace PhosphorylationStableCapacity
noncomputable section

/-- The literal physical readout, including the full printed measurement
error, lies in the first printed interval at every quarter-radius shift. -/
theorem operationalZero_measured_readout_interval
    (θ : Fin 21 → ℝ) (w : Fin 9 → ℝ) (measurement : ℝ)
    (hw : ‖w‖ ≤ (1/8192000 : ℝ)/4)
    (hmeasurement : |measurement| ≤ (1/1000 : ℝ)) :
    (23797/10000000 : ℝ) ≤
      operationalPhysicalReadout
        (fun i => (operationalZeroIntervalCoordinates i : ℝ))
        (fun i => (operationalZeroIntervalScales i : ℝ)) θ w+measurement ∧
    operationalPhysicalReadout
        (fun i => (operationalZeroIntervalCoordinates i : ℝ))
        (fun i => (operationalZeroIntervalScales i : ℝ)) θ w+measurement ≤
      (437971/100000000 : ℝ) := by
  have hcentre : (1/10 : ℝ)*
      ((operationalZeroIntervalCoordinates 2 : ℝ)+
        (operationalZeroIntervalCoordinates 8 : ℝ)) =
          (566751/167692250 : ℝ) := by
    norm_num [operationalZeroIntervalCoordinates]
  have hradius : (1/10 : ℝ)*
      ((operationalZeroIntervalScales 2 : ℝ)+
        (operationalZeroIntervalScales 8 : ℝ))*((1/8192000 : ℝ)/4)+
          (1/1000 : ℝ) = (5494940214751/5494939648000000 : ℝ) := by
    norm_num [operationalZeroIntervalScales]
  have herror := operationalPhysicalReadout_measurement_bound
    (fun i => (operationalZeroIntervalCoordinates i : ℝ))
    (fun i => (operationalZeroIntervalScales i : ℝ))
    (Rat.cast_nonneg.mpr (operationalZero_scales_positive 2).le)
    (Rat.cast_nonneg.mpr (operationalZero_scales_positive 8).le)
    θ w (1/8192000) measurement hw hmeasurement
  rw [hcentre, hradius] at herror
  apply measured_readout_mem_certified_interval
    (566751/167692250) _ (5494940214751/5494939648000000)
    (23797/10000000) (437971/100000000) herror
  · norm_num
  · norm_num

end
end PhosphorylationStableCapacity

/- Source component: BenchmarkOperationalRecoveryZero -/
namespace PhosphorylationStableCapacity
noncomputable section
open Matrix PhosphorylationSharpness
open scoped BigOperators

/-- Every physical solution in seconds from the printed inner ball obeys the
printed recovery envelope, under all21 independent parameter perturbations.
The same fixed rational P and the same equilibrium are used throughout. -/
theorem operationalZero_physical_forward_recovery
    (θ : Fin 21 → ℝ)
    (hθ : ∀ i : Fin 21,
      |θ i-(operationalZeroIntervalNominal (Fin.castAdd 9 i) : ℝ)| ≤
        (1/671088640000 : ℝ)*(operationalZeroIntervalNominal (Fin.castAdd 9 i) : ℝ))
    (equilibrium initial : Fin 9 → ℝ)
    (hshift : ‖equilibrium‖ ≤ (1/8192000 : ℝ)/4)
    (heq : operationalWeightedField
      (fun i => (operationalZeroIntervalCoordinates i : ℝ))
      (fun i => (operationalZeroIntervalScales i : ℝ)) θ equilibrium = 0)
    (hinit : (∑ i, (initial i-equilibrium i)^2) ≤ (1/16384000000 : ℝ)^2) :
    (∃ γ : ℝ → Fin 9 → ℝ,
      IsOperationalPhysicalCurve (fun i => (operationalZeroIntervalCoordinates i : ℝ))
        (fun i => (operationalZeroIntervalScales i : ℝ)) θ initial γ) ∧
    ∀ γ : ℝ → Fin 9 → ℝ,
      IsOperationalPhysicalCurve (fun i => (operationalZeroIntervalCoordinates i : ℝ))
        (fun i => (operationalZeroIntervalScales i : ℝ)) θ initial γ →
      (∀ t : ℝ, 0 ≤ t → ‖γ t‖ < (1/8192000 : ℝ)) ∧
      (∀ t : ℝ, 0 ≤ t → finiteEuclideanLength (γ t-equilibrium) ≤
        ((1/8192000 : ℝ)/2)*Real.exp
          (-((operationalZeroDecayMargin : ℝ)/(2*(operationalZeroPRowBound : ℝ)))*(t/10))) ∧
      (∀ t : ℝ, (357000 : ℝ) ≤ t →
        finiteEuclideanLength (γ t-equilibrium) < (1/8192000 : ℝ)/20) := by
  have hpositive : ∀ i, 0 < θ i := operational_independent_parameters_positive
    (fun i => operationalZeroIntervalNominal (Fin.castAdd 9 i)) (1/671088640000)
    θ operationalZero_nominal_parameters_positive (by norm_num)
    (by norm_num only [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]; exact hθ)
  have hspecies (w : Fin 9 → ℝ) (hw : ‖w‖ ≤ (1/8192000 : ℝ)) :
      ∀ i, 0 < operationalSpecies
        (fun j => (operationalZeroIntervalCoordinates j : ℝ))
        (fun j => (operationalZeroIntervalScales j : ℝ)) θ w i := by
    apply operational_actual_species_positive operationalZeroIntervalCoordinates
      operationalZeroIntervalScales operationalZeroIntervalDomain
      operationalZeroInterval_positive_species θ w
    rw [operationalZero_independent_domain_exact]
    exact operationalInput_mem_independent_domain _ _ _ θ w
      (by norm_num only [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]; exact hθ)
      (by norm_num only [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]; exact hw)
  have hmargin : (operationalZeroPRowBound : ℝ)*(1/16384000000 : ℝ)^2 <
      (1/100 : ℝ)*((1/8192000 : ℝ)/2)^2 := by
    norm_num [operationalZeroPRowBound]
  obtain ⟨⟨β, hβ⟩, hcertificate⟩ := operational_certified_forward_recovery
    operationalZeroIntervalCoordinates operationalZeroIntervalScales
    (fun i => (operationalZero_scales_positive i).ne') θ hpositive
    operationalZeroP.realMatrix operationalZeroP_posDef.isHermitian.isSymm
    equilibrium initial (1/8192000) (1/16384000000) (1/100)
    (operationalZeroDecayMargin : ℝ) (operationalZeroPRowBound : ℝ)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (Rat.cast_pos.mpr operationalZero_decay_margin_positive)
    (by norm_num [operationalZeroPRowBound]) hshift heq hspecies
    operationalZero_P_printed_lower operationalZero_P_upper
    (operationalZero_actual_uniform_dissipation θ hθ) hmargin hinit
  refine ⟨⟨fun t => β (t/10), operational_physical_curve_of_model _ _ θ initial β hβ⟩, ?_⟩
  intro γ hγ
  obtain ⟨hstay, henv, htime⟩ := operational_physical_recovery_of_model_certificate
    (fun i => (operationalZeroIntervalCoordinates i : ℝ))
    (fun i => (operationalZeroIntervalScales i : ℝ)) θ initial equilibrium
    (1/8192000) (operationalZeroDecayMargin : ℝ) (operationalZeroPRowBound : ℝ)
    hcertificate γ hγ
  refine ⟨hstay, henv, ?_⟩
  intro t ht
  apply htime t
  have hprinted : (60 : ℝ)*(operationalZeroPRowBound : ℝ)/
      (operationalZeroDecayMargin : ℝ) ≤ 357000 := by
    norm_num [operationalZeroPRowBound, operationalZeroDecayMargin]
  exact hprinted.trans ht

end
end PhosphorylationStableCapacity

namespace PhosphorylationStableCapacity
noncomputable section
open Matrix PhosphorylationSharpness
open scoped BigOperators

/-- The closed printed ellipsoid is invariant for every solution of the actual
physical equation, even when the initial energy is exactly the boundary value. -/
theorem operationalZero_physical_closed_ellipsoid
    (θ : Fin 21 → ℝ)
    (hθ : ∀ i : Fin 21,
      |θ i-(operationalZeroIntervalNominal (Fin.castAdd 9 i) : ℝ)| ≤
        (1/671088640000 : ℝ)*(operationalZeroIntervalNominal (Fin.castAdd 9 i) : ℝ))
    (equilibrium initial : Fin 9 → ℝ)
    (hshift : ‖equilibrium‖ ≤ (1/8192000 : ℝ)/4)
    (heq : operationalWeightedField
      (fun i => (operationalZeroIntervalCoordinates i : ℝ))
      (fun i => (operationalZeroIntervalScales i : ℝ)) θ equilibrium = 0)
    (hinit : (initial-equilibrium) ⬝ᵥ
      (operationalZeroP.realMatrix *ᵥ (initial-equilibrium)) ≤
        (1/100 : ℝ)*((1/8192000 : ℝ)/2)^2) :
    (∃ γ : ℝ → Fin 9 → ℝ,
      IsOperationalPhysicalCurve (fun i => (operationalZeroIntervalCoordinates i : ℝ))
        (fun i => (operationalZeroIntervalScales i : ℝ)) θ initial γ) ∧
    ∀ γ : ℝ → Fin 9 → ℝ,
      IsOperationalPhysicalCurve (fun i => (operationalZeroIntervalCoordinates i : ℝ))
        (fun i => (operationalZeroIntervalScales i : ℝ)) θ initial γ →
      (∀ t : ℝ, 0 ≤ t → (γ t-equilibrium) ⬝ᵥ
        (operationalZeroP.realMatrix *ᵥ (γ t-equilibrium)) ≤
          (1/100 : ℝ)*((1/8192000 : ℝ)/2)^2) ∧
      (∀ t : ℝ, 0 ≤ t → ‖γ t‖ < (1/8192000 : ℝ)) ∧
      (∀ t : ℝ, 0 ≤ t → finiteEuclideanLength (γ t-equilibrium) ≤
        ((1/8192000 : ℝ)/2)*Real.exp
          (-((operationalZeroDecayMargin : ℝ)/(2*(operationalZeroPRowBound : ℝ)))*(t/10))) ∧
      (∀ t : ℝ, (357000 : ℝ) ≤ t →
        finiteEuclideanLength (γ t-equilibrium) < (1/8192000 : ℝ)/20) := by
  have hpositive : ∀ i, 0 < θ i := operational_independent_parameters_positive
    (fun i => operationalZeroIntervalNominal (Fin.castAdd 9 i)) (1/671088640000)
    θ operationalZero_nominal_parameters_positive (by norm_num)
    (by norm_num only [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]; exact hθ)
  have hsumsq : (∑ i, (initial i-equilibrium i)^2) ≤
      ((1/8192000 : ℝ)/2)^2 := by
    have hlower := operationalZero_P_printed_lower (initial-equilibrium)
    simp only [Pi.sub_apply] at hlower
    nlinarith [hlower]
  have hdist : ‖initial-equilibrium‖ ≤ (1/8192000 : ℝ)/2 :=
    (sup_norm_le_finiteEuclideanLength (initial-equilibrium)).trans
      (Real.sqrt_le_iff.mpr ⟨by norm_num, hsumsq⟩)
  have hinitial : ‖initial‖ ≤ (1/8192000 : ℝ) := by
    have hi : initial = (initial-equilibrium)+equilibrium := by abel
    rw [hi]
    have hn := norm_add_le (initial-equilibrium) equilibrium
    linarith only [hn, hdist, hshift]
  have hspecies : ∀ i, 0 < operationalSpecies
      (fun j => (operationalZeroIntervalCoordinates j : ℝ))
      (fun j => (operationalZeroIntervalScales j : ℝ)) θ initial i := by
    apply operational_actual_species_positive operationalZeroIntervalCoordinates
      operationalZeroIntervalScales operationalZeroIntervalDomain
      operationalZeroInterval_positive_species θ initial
    rw [operationalZero_independent_domain_exact]
    exact operationalInput_mem_independent_domain _ _ _ θ initial
      (by norm_num only [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]; exact hθ)
      (by norm_num only [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]; exact hinitial)
  refine ⟨operational_exists_physical_forward_curve _ _
    (fun i => (operationalZero_scales_positive i).ne') θ hpositive initial hspecies, ?_⟩
  intro γ hγ
  obtain ⟨henergy, hstay, henv, htime⟩ := operational_certified_physical_closed_ellipsoid
    operationalZeroIntervalCoordinates operationalZeroIntervalScales θ
    operationalZeroP.realMatrix operationalZeroP_posDef.isHermitian.isSymm
    equilibrium (1/8192000) (1/100) (operationalZeroDecayMargin : ℝ)
    (operationalZeroPRowBound : ℝ) (by norm_num) (by norm_num)
    (Rat.cast_pos.mpr operationalZero_decay_margin_positive)
    (by norm_num [operationalZeroPRowBound]) hshift heq
    operationalZero_P_printed_lower operationalZero_P_upper
    (operationalZero_actual_uniform_dissipation θ hθ) initial γ hγ hinit
  refine ⟨henergy, hstay, henv, ?_⟩
  intro t ht
  apply htime t
  have hprinted : (60 : ℝ)*(operationalZeroPRowBound : ℝ)/
      (operationalZeroDecayMargin : ℝ) ≤ 357000 := by
    norm_num [operationalZeroPRowBound, operationalZeroDecayMargin]
  exact hprinted.trans ht

end
end PhosphorylationStableCapacity
