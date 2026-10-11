module
public import proofs.PhosphorylationStableCapacity.BenchmarkOperationalSemanticFour
public import proofs.PhosphorylationStableCapacity.OperationalCertifiedModel
public import proofs.PhosphorylationStableCapacity.OperationalSinkOutcome

@[expose] public section

/- Source component: BenchmarkOperationalEnergyFour -/
namespace PhosphorylationStableCapacity
noncomputable section
open Matrix
open scoped BigOperators

theorem operationalFour_J_eq_actual_nominal_jacobian :
    operationalFourJ.realMatrix =
      operationalReactionJacobian operationalFourIntervalCoordinates
        operationalFourIntervalScales
        (fun i : Fin 21 => (operationalFourIntervalNominal (Fin.castAdd 9 i) : ℝ)) 0 := by
  rw [operationalReactionJacobian_at_rational_centre,
    ← operationalFour_nominal_species_reconstruction_exact,
    ← operationalFour_rates_eq_independent_nominal_parameters,
    ScaledIntegerMatrix.realMatrix_eq_rational_cast]
  exact congrArg (fun A : Matrix (Fin 9) (Fin 9) ℚ => A.map (Rat.castHom ℝ))
    operationalFour_nominal_derivative_exact

theorem operationalFour_Q_eq_actual_nominal_lyapunov_form :
    operationalFourQ.realMatrix =
      -((operationalReactionJacobian operationalFourIntervalCoordinates
          operationalFourIntervalScales
          (fun i : Fin 21 => (operationalFourIntervalNominal (Fin.castAdd 9 i) : ℝ)) 0).transpose *
            operationalFourP.realMatrix +
        operationalFourP.realMatrix *
          operationalReactionJacobian operationalFourIntervalCoordinates
            operationalFourIntervalScales
            (fun i : Fin 21 => (operationalFourIntervalNominal (Fin.castAdd 9 i) : ℝ)) 0) := by
  rw [← operationalFour_J_eq_actual_nominal_jacobian,
    operationalFourPLyap_real_identity, neg_neg]

theorem operationalFour_P_operator_norm_exact :
    ‖matrixSupContinuousMap operationalFourP.realMatrix‖ =
      (operationalFourPRowBound : ℝ) := by
  apply matrixSupContinuousMap_norm_eq_row_max _ _
    (by norm_num [operationalFourPRowBound]) operationalFourP_absolute_rows
  obtain ⟨i, hi⟩ := operationalFour_P_row_max_attained
  refine ⟨i, ?_⟩
  rw [ScaledIntegerMatrix.realMatrix_eq_rational_cast]
  change (∑ j : Fin 9, |(operationalFourP.rationalMatrix i j : ℝ)|) = _
  exact_mod_cast hi

theorem operationalFour_QInverse_operator_norm_exact :
    ‖matrixSupContinuousMap operationalFourQInverse.realMatrix‖ =
      (operationalFourQInverseRowBound : ℝ) := by
  apply matrixSupContinuousMap_norm_eq_row_max _ _
    (by norm_num [operationalFourQInverseRowBound]) operationalFourQInverse_absolute_rows
  obtain ⟨i, hi⟩ := operationalFour_QInverse_row_max_attained
  refine ⟨i, ?_⟩
  rw [ScaledIntegerMatrix.realMatrix_eq_rational_cast]
  change (∑ j : Fin 9, |(operationalFourQInverse.rationalMatrix i j : ℝ)|) = _
  exact_mod_cast hi

theorem operationalFour_nominal_lyapunov_data :
    OperationalNominalLyapunovData operationalFourIntervalCoordinates
      operationalFourIntervalScales
      (fun i : Fin 21 => operationalFourIntervalNominal (Fin.castAdd 9 i))
      operationalFourP.realMatrix operationalFourQ.realMatrix
      operationalFourQInverse.realMatrix (operationalFourDecayMargin : ℝ)
      (4599501469907009612464002751315450826328711932522883905127728262836218206833047661497370341089714584554295941/245291609798590978623041458588212757858564254475582332674050107111671862729092679484239878553600000000000000000 : ℝ) := by
  refine ⟨operationalFour_Q_eq_actual_nominal_lyapunov_form,
    operationalFourQ_posDef, operationalFourQ_real_inverse, ?_,
    Rat.cast_pos.mpr operationalFour_decay_margin_positive⟩
  rw [operationalFour_QInverse_operator_norm_exact]
  norm_num [operationalFourDecayMargin, operationalFourQInverseRowBound]

theorem operationalFour_P_printed_lower (v : Fin 9 → ℝ) :
    (1/100 : ℝ)*(∑ i, v i^2) ≤ v ⬝ᵥ (operationalFourP.realMatrix *ᵥ v) := by
  have hc : (1/100 : ℝ) ≤ 1/(operationalFourPInverseRowBound : ℝ) := by
    norm_num [operationalFourPInverseRowBound]
  have hs : 0 ≤ ∑ i, v i^2 := Finset.sum_nonneg (fun i _ => sq_nonneg (v i))
  have hm := mul_le_mul_of_nonneg_right hc hs
  have hbound : (1/100 : ℝ)*(∑ i, v i^2) ≤
      (∑ i, v i^2)/(operationalFourPInverseRowBound : ℝ) := by
    simpa only [one_div, div_eq_mul_inv, mul_comm, one_mul] using hm
  exact hbound.trans (operationalFour_P_inverse_coercivity v)

/-- The printed positive decay constant bounds the actual nonlinear
Jacobian at every state and every independent parameter in the same box. -/
theorem operationalFour_actual_uniform_dissipation
    (θ : Fin 21 → ℝ)
    (hθ : ∀ i : Fin 21,
      |θ i-(operationalFourIntervalNominal (Fin.castAdd 9 i) : ℝ)| ≤
        (1/671088640000 : ℝ)*(operationalFourIntervalNominal (Fin.castAdd 9 i) : ℝ))
    (w : Fin 9 → ℝ) (hw : ‖w‖ ≤ (1/2048000 : ℝ)) (v : Fin 9 → ℝ) :
    2*(v ⬝ᵥ (operationalFourP.realMatrix *ᵥ
      (operationalReactionJacobian operationalFourIntervalCoordinates
        operationalFourIntervalScales θ w *ᵥ v))) ≤
      -(operationalFourDecayMargin : ℝ)*(∑ i, v i^2) := by
  have hC : (Matrix.of operationalFourIntervalLyapunovCoefficients).map (Rat.castHom ℝ) =
      operationalFourP.realMatrix *
        operationalWeightedStoichiometry (fun i => (operationalFourIntervalScales i : ℝ)) := by
    rw [ScaledIntegerMatrix.realMatrix_eq_rational_cast,
      operationalWeightedStoichiometry_eq_rational_cast, ← Matrix.map_mul]
    exact congrArg (fun A : Matrix (Fin 9) (Fin 18) ℚ => A.map (Rat.castHom ℝ))
      operationalFour_lyapunov_coefficients_exact
  have hJ : operationalFourJ.realMatrix =
      (operationalRationalStoichiometry operationalFourIntervalScales *
        operationalRationalDerivative operationalFourIntervalScales
          operationalFourIntervalNominalRates operationalFourIntervalNominalSpecies).map
            (Rat.castHom ℝ) := by
    rw [ScaledIntegerMatrix.realMatrix_eq_rational_cast]
    exact congrArg (fun A : Matrix (Fin 9) (Fin 9) ℚ => A.map (Rat.castHom ℝ))
      operationalFour_nominal_derivative_exact
  have hinput : ∀ i, (operationalFourIntervalDomain i).Contains
      (operationalInput θ w i) := by
    rw [operationalFour_independent_domain_exact]
    exact operationalInput_mem_independent_domain _ _ _ θ w
      (by norm_num only [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]; exact hθ)
      (by norm_num only [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]; exact hw)
  have hmargin : (operationalFourDecayMargin : ℝ) =
      (1 : ℝ)/(operationalFourQInverseRowBound : ℝ)-
      (4599501469907009612464002751315450826328711932522883905127728262836218206833047661497370341089714584554295941/245291609798590978623041458588212757858564254475582332674050107111671862729092679484239878553600000000000000000 : ℝ) := by
    norm_num [operationalFourDecayMargin, operationalFourQInverseRowBound]
  have h := operational_actual_lyapunov_dissipation
    (Matrix.of operationalFourIntervalLyapunovCoefficients)
    operationalFourIntervalCoordinates operationalFourIntervalScales
    operationalFourIntervalNominalRates operationalFourIntervalNominalSpecies
    operationalFourJ.realMatrix operationalFourP.realMatrix operationalFourQ.realMatrix
    operationalFourP_posDef.isHermitian.isSymm hC hJ operationalFourPLyap_real_identity
    (1/(operationalFourQInverseRowBound : ℝ))
    (fun u => by simpa only [one_div, div_eq_mul_inv, mul_comm, one_mul] using
      operationalFour_Q_inverse_coercivity u)
    operationalFourIntervalDomain
    (4599501469907009612464002751315450826328711932522883905127728262836218206833047661497370341089714584554295941/245291609798590978623041458588212757858564254475582332674050107111671862729092679484239878553600000000000000000 : ℚ)
    operationalFourInterval_decay_loss_rows θ w hinput v
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h
  rw [← hmargin] at h
  exact h

end
end PhosphorylationStableCapacity

/- Source component: BenchmarkOperationalPersistenceFour -/
namespace PhosphorylationStableCapacity
noncomputable section
open Matrix PhosphorylationSharpness
open scoped BigOperators

/-- The third printed operational box contains exactly one positive physical
equilibrium for every admitted independent perturbation of all21 parameters. -/
theorem operationalFour_positive_equilibrium_persistence
    (θ : Fin 21 → ℝ)
    (hθ : ∀ i : Fin 21,
      |θ i-(operationalFourIntervalNominal (Fin.castAdd 9 i) : ℝ)| ≤
        (1/671088640000 : ℝ)*
          (operationalFourIntervalNominal (Fin.castAdd 9 i) : ℝ)) :
    ∃ w : Fin 9 → ℝ, ‖w‖ ≤ (1/2048000 : ℝ)/4 ∧
      (unChart (θ 18) (θ 19) (θ 20)
        (ofCoordinateSpace
          (operationalUnpack (fun i => (operationalFourIntervalCoordinates i : ℝ))+
            operationalLift (fun i => (operationalFourIntervalScales i : ℝ)) w))).Positive ∧
      Equilibrium (operationalParameterRates θ)
        (unChart (θ 18) (θ 19) (θ 20)
          (ofCoordinateSpace
            (operationalUnpack (fun i => (operationalFourIntervalCoordinates i : ℝ))+
              operationalLift (fun i => (operationalFourIntervalScales i : ℝ)) w))) ∧
      ∀ v : Fin 9 → ℝ, ‖v‖ ≤ (1/2048000 : ℝ) →
        operationalWeightedField (fun i => (operationalFourIntervalCoordinates i : ℝ))
          (fun i => (operationalFourIntervalScales i : ℝ)) θ v = 0 → v = w := by
  have hC : (Matrix.of operationalFourIntervalNewtonCoefficients).map (Rat.castHom ℝ) =
      operationalFourJInverse.realMatrix *
        operationalWeightedStoichiometry (fun i => (operationalFourIntervalScales i : ℝ)) := by
    rw [ScaledIntegerMatrix.realMatrix_eq_rational_cast,
      operationalWeightedStoichiometry_eq_rational_cast, ← Matrix.map_mul]
    exact congrArg (fun A : Matrix (Fin 9) (Fin 18) ℚ => A.map (Rat.castHom ℝ))
      operationalFour_newton_coefficients_exact
  have hJ : operationalFourJ.realMatrix =
      (operationalRationalStoichiometry operationalFourIntervalScales *
        operationalRationalDerivative operationalFourIntervalScales
          operationalFourIntervalNominalRates operationalFourIntervalNominalSpecies).map
            (Rat.castHom ℝ) := by
    rw [ScaledIntegerMatrix.realMatrix_eq_rational_cast]
    exact congrArg (fun A : Matrix (Fin 9) (Fin 9) ℚ => A.map (Rat.castHom ℝ))
      operationalFour_nominal_derivative_exact
  have hbalanced : operationalWeightedStoichiometry
      (fun i => (operationalFourIntervalScales i : ℝ)) *ᵥ
        (fun a => (operationalNominalFlux operationalFourIntervalNominalRates
          operationalFourIntervalNominalSpecies a : ℝ)) = 0 := by
    rw [operationalWeightedStoichiometry_eq_rational_cast]
    ext i
    have h := congrArg (fun v : Fin 9 → ℚ => (v i : ℝ))
      operationalFour_nominal_flux_balance
    simp only [Pi.zero_apply, Rat.cast_zero] at h
    change (Rat.castHom ℝ) ((operationalRationalStoichiometry operationalFourIntervalScales *ᵥ
      operationalNominalFlux operationalFourIntervalNominalRates
        operationalFourIntervalNominalSpecies) i) = 0 at h
    rw [RingHom.map_mulVec] at h
    simpa only [Function.comp_def, Rat.coe_castHom, Pi.zero_apply] using h
  have hρ : ((1/2048000 : ℚ) : ℝ) = (1/2048000 : ℝ) := by norm_num
  rw [← hρ]
  apply operational_certified_positive_equilibrium
    (Matrix.of operationalFourIntervalNewtonCoefficients)
    operationalFourIntervalCoordinates operationalFourIntervalScales
    operationalFourIntervalNominalRates operationalFourIntervalNominalSpecies
    operationalFourJInverse.realMatrix operationalFourJ.realMatrix
    (fun i => (operationalFour_scales_positive i).ne') hC
    operationalFourJ_real_inverse hJ hbalanced operationalFourIntervalDomain
    (1/2048000) (3/32768000) (by norm_num) (by norm_num) (by norm_num)
  · exact operationalFourInterval_contraction_rows
  · exact operationalFourInterval_centre_shift
  · exact operationalFourInterval_positive_species
  · intro w hw
    rw [operationalFour_independent_domain_exact]
    exact operationalInput_mem_independent_domain _ _ _ θ w
      (by norm_num only [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]; exact hθ) hw

end
end PhosphorylationStableCapacity

/- Source component: BenchmarkOperationalReadoutFour -/
namespace PhosphorylationStableCapacity
noncomputable section

/-- The literal physical readout, including the full printed measurement
error, lies in the third printed interval at every quarter-radius shift. -/
theorem operationalFour_measured_readout_interval
    (θ : Fin 21 → ℝ) (w : Fin 9 → ℝ) (measurement : ℝ)
    (hw : ‖w‖ ≤ (1/2048000 : ℝ)/4)
    (hmeasurement : |measurement| ≤ (1/1000 : ℝ)) :
    (10757833/50000000 : ℝ) ≤
      operationalPhysicalReadout
        (fun i => (operationalFourIntervalCoordinates i : ℝ))
        (fun i => (operationalFourIntervalScales i : ℝ)) θ w+measurement ∧
    operationalPhysicalReadout
        (fun i => (operationalFourIntervalCoordinates i : ℝ))
        (fun i => (operationalFourIntervalScales i : ℝ)) θ w+measurement ≤
      (2714459/12500000 : ℝ) := by
  have hcentre : (1/10 : ℝ)*
      ((operationalFourIntervalCoordinates 2 : ℝ)+
        (operationalFourIntervalCoordinates 8 : ℝ)) =
          (11901771/55060850 : ℝ) := by
    norm_num [operationalFourIntervalCoordinates]
  have hradius : (1/10 : ℝ)*
      ((operationalFourIntervalScales 2 : ℝ)+
        (operationalFourIntervalScales 8 : ℝ))*((1/2048000 : ℝ)/4)+
          (1/1000 : ℝ) = (451070384971/451058483200000 : ℝ) := by
    norm_num [operationalFourIntervalScales]
  have herror := operationalPhysicalReadout_measurement_bound
    (fun i => (operationalFourIntervalCoordinates i : ℝ))
    (fun i => (operationalFourIntervalScales i : ℝ))
    (Rat.cast_nonneg.mpr (operationalFour_scales_positive 2).le)
    (Rat.cast_nonneg.mpr (operationalFour_scales_positive 8).le)
    θ w (1/2048000) measurement hw hmeasurement
  rw [hcentre, hradius] at herror
  apply measured_readout_mem_certified_interval
    (11901771/55060850) _ (451070384971/451058483200000)
    (10757833/50000000) (2714459/12500000) herror
  · norm_num
  · norm_num

end
end PhosphorylationStableCapacity

/- Source component: BenchmarkOperationalRecoveryFour -/
namespace PhosphorylationStableCapacity
noncomputable section
open Matrix PhosphorylationSharpness
open scoped BigOperators

/-- Every physical solution in seconds from the printed inner ball obeys the
printed recovery envelope, under all21 independent parameter perturbations.
The same fixed rational P and the same equilibrium are used throughout. -/
theorem operationalFour_physical_forward_recovery
    (θ : Fin 21 → ℝ)
    (hθ : ∀ i : Fin 21,
      |θ i-(operationalFourIntervalNominal (Fin.castAdd 9 i) : ℝ)| ≤
        (1/671088640000 : ℝ)*(operationalFourIntervalNominal (Fin.castAdd 9 i) : ℝ))
    (equilibrium initial : Fin 9 → ℝ)
    (hshift : ‖equilibrium‖ ≤ (1/2048000 : ℝ)/4)
    (heq : operationalWeightedField
      (fun i => (operationalFourIntervalCoordinates i : ℝ))
      (fun i => (operationalFourIntervalScales i : ℝ)) θ equilibrium = 0)
    (hinit : (∑ i, (initial i-equilibrium i)^2) ≤ (1/40960000000 : ℝ)^2) :
    (∃ γ : ℝ → Fin 9 → ℝ,
      IsOperationalPhysicalCurve (fun i => (operationalFourIntervalCoordinates i : ℝ))
        (fun i => (operationalFourIntervalScales i : ℝ)) θ initial γ) ∧
    ∀ γ : ℝ → Fin 9 → ℝ,
      IsOperationalPhysicalCurve (fun i => (operationalFourIntervalCoordinates i : ℝ))
        (fun i => (operationalFourIntervalScales i : ℝ)) θ initial γ →
      (∀ t : ℝ, 0 ≤ t → ‖γ t‖ < (1/2048000 : ℝ)) ∧
      (∀ t : ℝ, 0 ≤ t → finiteEuclideanLength (γ t-equilibrium) ≤
        ((1/2048000 : ℝ)/2)*Real.exp
          (-((operationalFourDecayMargin : ℝ)/(2*(operationalFourPRowBound : ℝ)))*(t/10))) ∧
      (∀ t : ℝ, (23433000 : ℝ) ≤ t →
        finiteEuclideanLength (γ t-equilibrium) < (1/2048000 : ℝ)/20) := by
  have hpositive : ∀ i, 0 < θ i := operational_independent_parameters_positive
    (fun i => operationalFourIntervalNominal (Fin.castAdd 9 i)) (1/671088640000)
    θ operationalFour_nominal_parameters_positive (by norm_num)
    (by norm_num only [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]; exact hθ)
  have hspecies (w : Fin 9 → ℝ) (hw : ‖w‖ ≤ (1/2048000 : ℝ)) :
      ∀ i, 0 < operationalSpecies
        (fun j => (operationalFourIntervalCoordinates j : ℝ))
        (fun j => (operationalFourIntervalScales j : ℝ)) θ w i := by
    apply operational_actual_species_positive operationalFourIntervalCoordinates
      operationalFourIntervalScales operationalFourIntervalDomain
      operationalFourInterval_positive_species θ w
    rw [operationalFour_independent_domain_exact]
    exact operationalInput_mem_independent_domain _ _ _ θ w
      (by norm_num only [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]; exact hθ)
      (by norm_num only [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]; exact hw)
  have hmargin : (operationalFourPRowBound : ℝ)*(1/40960000000 : ℝ)^2 <
      (1/100 : ℝ)*((1/2048000 : ℝ)/2)^2 := by
    norm_num [operationalFourPRowBound]
  obtain ⟨⟨β, hβ⟩, hcertificate⟩ := operational_certified_forward_recovery
    operationalFourIntervalCoordinates operationalFourIntervalScales
    (fun i => (operationalFour_scales_positive i).ne') θ hpositive
    operationalFourP.realMatrix operationalFourP_posDef.isHermitian.isSymm
    equilibrium initial (1/2048000) (1/40960000000) (1/100)
    (operationalFourDecayMargin : ℝ) (operationalFourPRowBound : ℝ)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (Rat.cast_pos.mpr operationalFour_decay_margin_positive)
    (by norm_num [operationalFourPRowBound]) hshift heq hspecies
    operationalFour_P_printed_lower operationalFour_P_upper
    (operationalFour_actual_uniform_dissipation θ hθ) hmargin hinit
  refine ⟨⟨fun t => β (t/10), operational_physical_curve_of_model _ _ θ initial β hβ⟩, ?_⟩
  intro γ hγ
  obtain ⟨hstay, henv, htime⟩ := operational_physical_recovery_of_model_certificate
    (fun i => (operationalFourIntervalCoordinates i : ℝ))
    (fun i => (operationalFourIntervalScales i : ℝ)) θ initial equilibrium
    (1/2048000) (operationalFourDecayMargin : ℝ) (operationalFourPRowBound : ℝ)
    hcertificate γ hγ
  refine ⟨hstay, henv, ?_⟩
  intro t ht
  apply htime t
  have hprinted : (60 : ℝ)*(operationalFourPRowBound : ℝ)/
      (operationalFourDecayMargin : ℝ) ≤ 23433000 := by
    norm_num [operationalFourPRowBound, operationalFourDecayMargin]
  exact hprinted.trans ht

end
end PhosphorylationStableCapacity

namespace PhosphorylationStableCapacity
noncomputable section
open Matrix PhosphorylationSharpness
open scoped BigOperators

/-- The closed printed ellipsoid is invariant for every solution of the actual
physical equation, even when the initial energy is exactly the boundary value. -/
theorem operationalFour_physical_closed_ellipsoid
    (θ : Fin 21 → ℝ)
    (hθ : ∀ i : Fin 21,
      |θ i-(operationalFourIntervalNominal (Fin.castAdd 9 i) : ℝ)| ≤
        (1/671088640000 : ℝ)*(operationalFourIntervalNominal (Fin.castAdd 9 i) : ℝ))
    (equilibrium initial : Fin 9 → ℝ)
    (hshift : ‖equilibrium‖ ≤ (1/2048000 : ℝ)/4)
    (heq : operationalWeightedField
      (fun i => (operationalFourIntervalCoordinates i : ℝ))
      (fun i => (operationalFourIntervalScales i : ℝ)) θ equilibrium = 0)
    (hinit : (initial-equilibrium) ⬝ᵥ
      (operationalFourP.realMatrix *ᵥ (initial-equilibrium)) ≤
        (1/100 : ℝ)*((1/2048000 : ℝ)/2)^2) :
    (∃ γ : ℝ → Fin 9 → ℝ,
      IsOperationalPhysicalCurve (fun i => (operationalFourIntervalCoordinates i : ℝ))
        (fun i => (operationalFourIntervalScales i : ℝ)) θ initial γ) ∧
    ∀ γ : ℝ → Fin 9 → ℝ,
      IsOperationalPhysicalCurve (fun i => (operationalFourIntervalCoordinates i : ℝ))
        (fun i => (operationalFourIntervalScales i : ℝ)) θ initial γ →
      (∀ t : ℝ, 0 ≤ t → (γ t-equilibrium) ⬝ᵥ
        (operationalFourP.realMatrix *ᵥ (γ t-equilibrium)) ≤
          (1/100 : ℝ)*((1/2048000 : ℝ)/2)^2) ∧
      (∀ t : ℝ, 0 ≤ t → ‖γ t‖ < (1/2048000 : ℝ)) ∧
      (∀ t : ℝ, 0 ≤ t → finiteEuclideanLength (γ t-equilibrium) ≤
        ((1/2048000 : ℝ)/2)*Real.exp
          (-((operationalFourDecayMargin : ℝ)/(2*(operationalFourPRowBound : ℝ)))*(t/10))) ∧
      (∀ t : ℝ, (23433000 : ℝ) ≤ t →
        finiteEuclideanLength (γ t-equilibrium) < (1/2048000 : ℝ)/20) := by
  have hpositive : ∀ i, 0 < θ i := operational_independent_parameters_positive
    (fun i => operationalFourIntervalNominal (Fin.castAdd 9 i)) (1/671088640000)
    θ operationalFour_nominal_parameters_positive (by norm_num)
    (by norm_num only [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]; exact hθ)
  have hsumsq : (∑ i, (initial i-equilibrium i)^2) ≤
      ((1/2048000 : ℝ)/2)^2 := by
    have hlower := operationalFour_P_printed_lower (initial-equilibrium)
    simp only [Pi.sub_apply] at hlower
    nlinarith [hlower]
  have hdist : ‖initial-equilibrium‖ ≤ (1/2048000 : ℝ)/2 :=
    (sup_norm_le_finiteEuclideanLength (initial-equilibrium)).trans
      (Real.sqrt_le_iff.mpr ⟨by norm_num, hsumsq⟩)
  have hinitial : ‖initial‖ ≤ (1/2048000 : ℝ) := by
    have hi : initial = (initial-equilibrium)+equilibrium := by abel
    rw [hi]
    have hn := norm_add_le (initial-equilibrium) equilibrium
    linarith only [hn, hdist, hshift]
  have hspecies : ∀ i, 0 < operationalSpecies
      (fun j => (operationalFourIntervalCoordinates j : ℝ))
      (fun j => (operationalFourIntervalScales j : ℝ)) θ initial i := by
    apply operational_actual_species_positive operationalFourIntervalCoordinates
      operationalFourIntervalScales operationalFourIntervalDomain
      operationalFourInterval_positive_species θ initial
    rw [operationalFour_independent_domain_exact]
    exact operationalInput_mem_independent_domain _ _ _ θ initial
      (by norm_num only [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]; exact hθ)
      (by norm_num only [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]; exact hinitial)
  refine ⟨operational_exists_physical_forward_curve _ _
    (fun i => (operationalFour_scales_positive i).ne') θ hpositive initial hspecies, ?_⟩
  intro γ hγ
  obtain ⟨henergy, hstay, henv, htime⟩ := operational_certified_physical_closed_ellipsoid
    operationalFourIntervalCoordinates operationalFourIntervalScales θ
    operationalFourP.realMatrix operationalFourP_posDef.isHermitian.isSymm
    equilibrium (1/2048000) (1/100) (operationalFourDecayMargin : ℝ)
    (operationalFourPRowBound : ℝ) (by norm_num) (by norm_num)
    (Rat.cast_pos.mpr operationalFour_decay_margin_positive)
    (by norm_num [operationalFourPRowBound]) hshift heq
    operationalFour_P_printed_lower operationalFour_P_upper
    (operationalFour_actual_uniform_dissipation θ hθ) initial γ hγ hinit
  refine ⟨henergy, hstay, henv, ?_⟩
  intro t ht
  apply htime t
  have hprinted : (60 : ℝ)*(operationalFourPRowBound : ℝ)/
      (operationalFourDecayMargin : ℝ) ≤ 23433000 := by
    norm_num [operationalFourPRowBound, operationalFourDecayMargin]
  exact hprinted.trans ht

end
end PhosphorylationStableCapacity
