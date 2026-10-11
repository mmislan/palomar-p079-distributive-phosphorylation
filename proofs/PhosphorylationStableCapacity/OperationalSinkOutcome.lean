module
public import proofs.PhosphorylationStableCapacity.OperationalCertifiedModel
public import Mathlib.LinearAlgebra.Matrix.PosDef

@[expose] public section

namespace PhosphorylationStableCapacity
noncomputable section
open Matrix PhosphorylationSharpness
open scoped BigOperators

/-- The nominal decay matrix is formed from the actual nominal Jacobian;
its inverse norm gives the same positive decay constant used in recovery. -/
structure OperationalNominalLyapunovData (q s : Fin 9 → ℚ) (nominal : Fin 21 → ℚ)
    (P Q Qinv : Matrix (Fin 9) (Fin 9) ℝ) (c loss : ℝ) : Prop where
  actual_nominal_form : Q =
    -((operationalReactionJacobian q s (fun i => (nominal i : ℝ)) 0).transpose*P +
      P*operationalReactionJacobian q s (fun i => (nominal i : ℝ)) 0)
  positive_definite : Q.PosDef
  exact_inverse : Q*Qinv = 1
  decay_formula : c = 1/‖matrixSupContinuousMap Qinv‖-loss
  decay_positive : 0 < c

/-- The recovery conclusion in seconds for the actual physical equation. -/
def OperationalRecoveryConclusion (equilibrium : Fin 9 → ℝ) (ρ c M recoveryTime : ℝ)
    (γ : ℝ → Fin 9 → ℝ) : Prop :=
  (∀ t : ℝ, 0 ≤ t → ‖γ t‖ < ρ) ∧
  (∀ t : ℝ, 0 ≤ t → finiteEuclideanLength (γ t-equilibrium) ≤
    (ρ/2)*Real.exp (-(c/(2*M))*(t/10))) ∧
  (∀ t : ℝ, recoveryTime ≤ t → finiteEuclideanLength (γ t-equilibrium) < ρ/20)

/-- A full operational certificate preserves the same equilibrium, all21
independently varying inputs, fixed P, and actual physical equation throughout.
The closed energy sublevel includes its boundary. -/
structure OperationalSinkOutcome (q s : Fin 9 → ℝ) (θ : Fin 21 → ℝ)
    (P : Matrix (Fin 9) (Fin 9) ℝ) (ρ ρin p c M recoveryTime lower upper : ℝ)
    (equilibrium : Fin 9 → ℝ) : Prop where
  physical_parameters_positive : ∀ i, 0 < operationalPhysicalParameters θ i
  physical_species_positive_in_box : ∀ w : Fin 9 → ℝ, ‖w‖ ≤ ρ →
    (operationalPhysicalState q s θ w).Positive
  positive_definite : P.PosDef
  rational_matrix : ∀ i j, ∃ a : ℚ, (a : ℝ) = P i j
  operator_norm : ‖matrixSupContinuousMap P‖ = M
  lower_constant_positive : 0 < p
  decay_positive : 0 < c
  quadratic_lower : ∀ v : Fin 9 → ℝ, p*(∑ i, v i^2) ≤ v ⬝ᵥ (P *ᵥ v)
  quadratic_upper : ∀ v : Fin 9 → ℝ, v ⬝ᵥ (P *ᵥ v) ≤ M*(∑ i, v i^2)
  actual_uniform_dissipation : ∀ w : Fin 9 → ℝ, ‖w‖ ≤ ρ →
    ∀ v : Fin 9 → ℝ, 2*(v ⬝ᵥ (P *ᵥ (operationalWeightedJacobian q s θ w v))) ≤
      -c*(∑ i, v i^2)
  shift : ‖equilibrium‖ ≤ ρ/4
  zero : operationalWeightedField q s θ equilibrium = 0
  positive : (operationalPhysicalState q s θ equilibrium).Positive
  physical_equilibrium : Equilibrium
    (operationalParameterRates (operationalPhysicalParameters θ))
      (operationalPhysicalState q s θ equilibrium)
  physical_class : InClass (operationalPhysicalParameters θ 18)
    (operationalPhysicalParameters θ 19) (operationalPhysicalParameters θ 20)
    (operationalPhysicalState q s θ equilibrium)
  unique_in_box : ∀ v : Fin 9 → ℝ, ‖v‖ ≤ ρ →
    operationalWeightedField q s θ v = 0 → v = equilibrium
  measured_readout : ∀ measurement : ℝ, |measurement| ≤ (1/1000 : ℝ) →
    lower ≤ operationalPhysicalReadout q s θ equilibrium+measurement ∧
      operationalPhysicalReadout q s θ equilibrium+measurement ≤ upper
  inner_recovery : ∀ initial : Fin 9 → ℝ,
    (∑ i, (initial i-equilibrium i)^2) ≤ ρin^2 →
    (∃ γ : ℝ → Fin 9 → ℝ, IsOperationalPhysicalCurve q s θ initial γ) ∧
    ∀ γ : ℝ → Fin 9 → ℝ, IsOperationalPhysicalCurve q s θ initial γ →
      OperationalRecoveryConclusion equilibrium ρ c M recoveryTime γ
  closed_ellipsoid_recovery : ∀ initial : Fin 9 → ℝ,
    (initial-equilibrium) ⬝ᵥ (P *ᵥ (initial-equilibrium)) ≤ p*(ρ/2)^2 →
    (∃ γ : ℝ → Fin 9 → ℝ, IsOperationalPhysicalCurve q s θ initial γ) ∧
    ∀ γ : ℝ → Fin 9 → ℝ, IsOperationalPhysicalCurve q s θ initial γ →
      (∀ t : ℝ, 0 ≤ t → (γ t-equilibrium) ⬝ᵥ
        (P *ᵥ (γ t-equilibrium)) ≤ p*(ρ/2)^2) ∧
      OperationalRecoveryConclusion equilibrium ρ c M recoveryTime γ

/-- The printed fixed matrix determines the nominal decay matrix; its inverse
is constrained by the exact inverse identity rather than an auxiliary table. -/
def OperationalPrintedSinkOutcome (q s : Fin 9 → ℚ) (nominal : Fin 21 → ℚ)
    (θ : Fin 21 → ℝ) (P : Matrix (Fin 9) (Fin 9) ℝ)
    (ρ ρin p c M recoveryTime lower upper loss : ℝ) (equilibrium : Fin 9 → ℝ) : Prop :=
  ∃ Q Qinv : Matrix (Fin 9) (Fin 9) ℝ,
    OperationalNominalLyapunovData q s (fun i => nominal i) P Q Qinv c loss ∧
    OperationalSinkOutcome (fun i => (q i : ℝ)) (fun i => (s i : ℝ)) θ
      P ρ ρin p c M recoveryTime lower upper equilibrium

/-- Disjoint certified readout intervals force distinct actual physical states. -/
theorem OperationalSinkOutcome.physical_state_ne
    {q s q' s' : Fin 9 → ℝ} {θ : Fin 21 → ℝ}
    {P P' : Matrix (Fin 9) (Fin 9) ℝ}
    {ρ ρin p c M T lower upper ρ' ρin' p' c' M' T' lower' upper' : ℝ}
    {equilibrium equilibrium' : Fin 9 → ℝ}
    (h : OperationalSinkOutcome q s θ P ρ ρin p c M T lower upper equilibrium)
    (h' : OperationalSinkOutcome q' s' θ P' ρ' ρin' p' c' M' T' lower' upper' equilibrium')
    (hsep : upper < lower') :
    operationalPhysicalState q s θ equilibrium ≠
      operationalPhysicalState q' s' θ equilibrium' := by
  intro heq
  have hr := congrArg (fun x : State 3 => x.S 3+x.D 2) heq
  have hread : operationalPhysicalReadout q s θ equilibrium =
      operationalPhysicalReadout q' s' θ equilibrium' := by
    rw [operationalPhysicalReadout_eq_converted_state,
      operationalPhysicalReadout_eq_converted_state]
    exact hr
  have hu := (h.measured_readout 0 (by norm_num)).2
  have hl := (h'.measured_readout 0 (by norm_num)).1
  simp only [add_zero] at hu hl
  rw [hread] at hu
  exact (hsep.trans_le hl).not_ge hu

end
end PhosphorylationStableCapacity
