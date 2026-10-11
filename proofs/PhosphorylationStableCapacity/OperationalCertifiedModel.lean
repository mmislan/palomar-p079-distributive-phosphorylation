module
public import proofs.PhosphorylationStableCapacity.OperationalWeightedCoordinates
public import proofs.PhosphorylationStableCapacity.OperationalCertificateAlgebra
public import proofs.PhosphorylationStableCapacity.QuantitativeMatrixDissipation
public import proofs.PhosphorylationStableCapacity.OperationalReadoutEnvelope
public import proofs.PhosphorylationStableCapacity.CertifiedNewtonPersistence
public import proofs.PhosphorylationStableCapacity.CertifiedQuadraticRecovery
public import proofs.PhosphorylationStableCapacity.FiniteEuclideanLength
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.NormNum
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import proofs.PhosphorylationStableCapacity.CertifiedClosedQuadraticRecovery

@[expose] public section

set_option maxHeartbeats 2000000

namespace PhosphorylationStableCapacity
noncomputable section
open Set

/-- The actual weighted mass-action equation in seconds, with the manuscript's
fixed ten-second model-time unit. -/
def IsOperationalPhysicalCurve (q s : Fin 9 → ℝ) (θ : Fin 21 → ℝ)
    (initial : Fin 9 → ℝ) (γ : ℝ → Fin 9 → ℝ) : Prop :=
  γ 0 = initial ∧ ∀ t : ℝ, 0 ≤ t →
    HasDerivWithinAt γ ((1/10 : ℝ) • operationalWeightedField q s θ (γ t))
      (Ici (0 : ℝ)) t

theorem operational_physical_curve_of_model
    (q s : Fin 9 → ℝ) (θ : Fin 21 → ℝ) (initial : Fin 9 → ℝ)
    (γ : ℝ → Fin 9 → ℝ) (hγ : IsOperationalForwardCurve q s θ initial γ) :
    IsOperationalPhysicalCurve q s θ initial (fun t => γ (t/10)) := by
  refine ⟨by simpa using hγ.1, ?_⟩
  intro t ht
  have htime : HasDerivWithinAt (fun u : ℝ => u/10) (1/10 : ℝ)
      (Ici (0 : ℝ)) t := by
    simpa using ((hasDerivAt_id t).div_const (10 : ℝ)).hasDerivWithinAt
  have hcalc := (hγ.2 (t/10) (div_nonneg ht (by norm_num))).scomp t htime
    (fun u hu => div_nonneg hu (by norm_num))
  exact hcalc

theorem operational_model_curve_of_physical
    (q s : Fin 9 → ℝ) (θ : Fin 21 → ℝ) (initial : Fin 9 → ℝ)
    (γ : ℝ → Fin 9 → ℝ) (hγ : IsOperationalPhysicalCurve q s θ initial γ) :
    IsOperationalForwardCurve q s θ initial (fun t => γ (10*t)) := by
  refine ⟨by simpa using hγ.1, ?_⟩
  intro t ht
  have htime : HasDerivWithinAt (fun u : ℝ => 10*u) (10 : ℝ)
      (Ici (0 : ℝ)) t := by
    simpa using ((hasDerivAt_id t).const_mul (10 : ℝ)).hasDerivWithinAt
  have hcalc := (hγ.2 (10*t) (mul_nonneg (by norm_num) ht)).scomp t htime
    (fun (u : ℝ) (hu : u ∈ Ici (0 : ℝ)) =>
      show 10*u ∈ Ici (0 : ℝ) from mul_nonneg (by norm_num : (0 : ℝ) ≤ 10) hu)
  simpa only [Function.comp_def, smul_smul,
    show (10 : ℝ)*(1/10) = 1 by norm_num, one_smul] using hcalc

/-- The paper fixes C₀=0.1 micromolar and T₀=10 seconds. Association rates
retain their numerical values because C₀T₀=1; the other rates and the totals
are divided by ten. This invertible map preserves all21 independent inputs. -/
def operationalPhysicalParameters (θ : Fin 21 → ℝ) : Fin 21 → ℝ :=
  fun i => if i.val < 18 ∧ i.val % 3 = 0 then θ i else θ i/10

def operationalModelParameters (θ : Fin 21 → ℝ) : Fin 21 → ℝ :=
  fun i => if i.val < 18 ∧ i.val % 3 = 0 then θ i else 10*θ i

theorem operationalPhysicalParameters_positive
    (θ : Fin 21 → ℝ) (hθ : ∀ i, 0 < θ i) :
    ∀ i, 0 < operationalPhysicalParameters θ i := by
  intro i
  by_cases hi : i.val < 18 ∧ i.val % 3 = 0
  · simpa only [operationalPhysicalParameters, ite_eq_left hi] using hθ i
  · simpa only [operationalPhysicalParameters, ite_eq_right hi] using
      div_pos (hθ i) (by norm_num : (0 : ℝ) < 10)

theorem operationalModelParameters_physical (θ : Fin 21 → ℝ) :
    operationalModelParameters (operationalPhysicalParameters θ) = θ := by
  ext i
  fin_cases i <;> simp [operationalModelParameters, operationalPhysicalParameters]
  all_goals ring

theorem operationalPhysicalParameters_model (θ : Fin 21 → ℝ) :
    operationalPhysicalParameters (operationalModelParameters θ) = θ := by
  ext i
  fin_cases i <;> simp [operationalModelParameters, operationalPhysicalParameters]

/-- Conversion of units preserves the complete relative box, coordinate by
coordinate; none of the eighteen rates or three totals is tied to another. -/
theorem operational_physical_relative_box_iff
    (nominal θ : Fin 21 → ℝ) (η : ℝ) :
    (∀ i, |operationalPhysicalParameters θ i -
      operationalPhysicalParameters nominal i| ≤
        η * operationalPhysicalParameters nominal i) ↔
    (∀ i, |θ i - nominal i| ≤ η * nominal i) := by
  have hpoint (i : Fin 21) :
      (|operationalPhysicalParameters θ i -
        operationalPhysicalParameters nominal i| ≤
          η * operationalPhysicalParameters nominal i) ↔
      (|θ i - nominal i| ≤ η * nominal i) := by
    by_cases hi : i.val < 18 ∧ i.val % 3 = 0
    · simp only [operationalPhysicalParameters, ite_eq_left hi]
    · simp only [operationalPhysicalParameters, ite_eq_right hi,
        ← sub_div, abs_div, show |(10 : ℝ)| = 10 by norm_num,
        ← mul_div_assoc, div_le_div_iff_of_pos_right (by norm_num : (0 : ℝ) < 10)]
  exact forall_congr' hpoint

theorem operational_physical_weighted_field
    (q s : Fin 9 → ℝ) (hs : ∀ i, s i ≠ 0) (θ : Fin 21 → ℝ) (w : Fin 9 → ℝ) :
    operationalWeightedField (fun i => q i/10) (fun i => s i/10)
      (operationalPhysicalParameters θ) w =
        (1/10 : ℝ) • operationalWeightedField q s θ w := by
  ext i
  fin_cases i <;>
    simp [operationalWeightedField, operationalRead_apply,
      restrictedFieldEuclid_threeSite, operationalFlatten,
      operationalUnpack, operationalLift_apply, operationalPhysicalParameters,
      operationalParameterRates, threeSiteField, threeSiteFreeS0,
      threeSiteFreeE, threeSiteFreeF]
  all_goals field_simp [hs]

theorem operational_physical_curve_iff_converted_mass_action
    (q s : Fin 9 → ℝ) (hs : ∀ i, s i ≠ 0) (θ : Fin 21 → ℝ)
    (initial : Fin 9 → ℝ) (γ : ℝ → Fin 9 → ℝ) :
    IsOperationalPhysicalCurve q s θ initial γ ↔
      IsOperationalForwardCurve (fun i => q i/10) (fun i => s i/10)
        (operationalPhysicalParameters θ) initial γ := by
  unfold IsOperationalPhysicalCurve IsOperationalForwardCurve
  simp_rw [operational_physical_weighted_field q s hs θ]

theorem operational_physical_species
    (q s : Fin 9 → ℝ) (θ : Fin 21 → ℝ) (w : Fin 9 → ℝ) :
    operationalSpecies (fun i => q i/10) (fun i => s i/10)
      (operationalPhysicalParameters θ) w =
        fun i => operationalSpecies q s θ w i/10 := by
  ext i
  fin_cases i <;>
    simp [operationalSpecies, operationalUnpack, operationalLift_apply,
      operationalPhysicalParameters, threeSiteFreeS0, threeSiteFreeE,
      threeSiteFreeF] <;> ring

end
end PhosphorylationStableCapacity



namespace PhosphorylationStableCapacity
noncomputable section
open Matrix
open scoped BigOperators

def operationalReactionJacobian (q s : Fin 9 → ℚ) (θ : Fin 21 → ℝ)
    (w : Fin 9 → ℝ) : Matrix (Fin 9) (Fin 9) ℝ :=
  operationalWeightedStoichiometry (fun i => (s i : ℝ)) *
    (Matrix.of fun a j => operationalReactionDerivative θ
      (operationalSpecies (fun i => (q i : ℝ)) (fun i => (s i : ℝ)) θ w)
      (fun i j => (operationalSpeciesLinear s i j : ℝ)) a j)

theorem operationalReactionJacobian_action
    (q s : Fin 9 → ℚ) (θ : Fin 21 → ℝ) (w v : Fin 9 → ℝ) :
    operationalWeightedJacobian (fun i => (q i : ℝ))
      (fun i => (s i : ℝ)) θ w v = operationalReactionJacobian q s θ w *ᵥ v :=
  operationalWeightedJacobian_reaction_action q s θ w v

theorem operationalReactionJacobian_midpoint
    (q s : Fin 9 → ℚ) (θ : Fin 21 → ℝ) (x v : Fin 9 → ℝ) :
    operationalWeightedField (fun i => (q i : ℝ)) (fun i => (s i : ℝ)) θ (x+v) -
      operationalWeightedField (fun i => (q i : ℝ)) (fun i => (s i : ℝ)) θ x =
      operationalReactionJacobian q s θ (x+(1/2 : ℝ) • v) *ᵥ v := by
  rw [operationalWeightedField_midpoint, operationalReactionJacobian_action]

theorem operationalWeightedStoichiometry_eq_rational_cast (s : Fin 9 → ℚ) :
    operationalWeightedStoichiometry (fun i => (s i : ℝ)) =
      (operationalRationalStoichiometry s).map (Rat.castHom ℝ) := by
  ext i a
  fin_cases i <;> fin_cases a <;>
    simp [operationalWeightedStoichiometry, operationalStoichiometry,
      operationalRationalStoichiometry, Matrix.map_apply]

theorem operationalRationalDerivative_cast
    (s : Fin 9 → ℚ) (rates : Fin 18 → ℚ) (x : Fin 12 → ℚ) (a : Fin 18) (j : Fin 9) :
    (operationalRationalDerivative s rates x a j : ℝ) =
      (operationalNominalReactionDerivative rates x (operationalSpeciesLinear s) a j : ℝ) := by
  rfl

theorem operationalSpecies_at_rational_centre
    (q s : Fin 9 → ℚ) (nominal : Fin 21 → ℚ) :
    operationalSpecies (fun i => (q i : ℝ)) (fun i => (s i : ℝ))
      (fun i => (nominal i : ℝ)) 0 =
        fun i => (operationalRationalCentreSpecies q nominal i : ℝ) := by
  ext i
  fin_cases i <;>
    norm_num [operationalSpecies, operationalRationalCentreSpecies,
      operationalUnpack, operationalLift_apply, threeSiteFreeS0,
      threeSiteFreeE, threeSiteFreeF, Fin.sum_univ_succ]

theorem operationalReactionDerivative_at_rational_parameters
    (s : Fin 9 → ℚ) (nominal : Fin 21 → ℚ) (x : Fin 12 → ℚ)
    (a : Fin 18) (j : Fin 9) :
    operationalReactionDerivative (fun i => (nominal i : ℝ))
      (fun i => (x i : ℝ)) (Matrix.of fun i j => (operationalSpeciesLinear s i j : ℝ))
        a j =
      (operationalRationalDerivative s (fun b => nominal (Fin.castAdd 3 b)) x a j : ℝ) := by
  cases hsecond : operationalReactionSecond a <;>
    simp [operationalReactionDerivative, operationalRationalDerivative, hsecond]

/-- The nominal rational matrix is the actual Jacobian at the reconstructed
nominal centre, rather than a separate supporting matrix. -/
theorem operationalReactionJacobian_at_rational_centre
    (q s : Fin 9 → ℚ) (nominal : Fin 21 → ℚ) :
    operationalReactionJacobian q s (fun i => (nominal i : ℝ)) 0 =
      (operationalRationalStoichiometry s *
        operationalRationalDerivative s (fun a => nominal (Fin.castAdd 3 a))
          (operationalRationalCentreSpecies q nominal)).map (Rat.castHom ℝ) := by
  unfold operationalReactionJacobian
  rw [operationalSpecies_at_rational_centre,
    operationalWeightedStoichiometry_eq_rational_cast, Matrix.map_mul]
  congr 1
  ext a j
  exact operationalReactionDerivative_at_rational_parameters s nominal _ a j

/-- The perturbed derivative matrix in every interval entry is the exact
perturbation of the same actual reaction Jacobian. -/
theorem operationalReactionJacobian_perturbation
    (q s : Fin 9 → ℚ) (rates : Fin 18 → ℚ) (x : Fin 12 → ℚ)
    (J₀ : Matrix (Fin 9) (Fin 9) ℝ)
    (hJ₀ : J₀ = (operationalRationalStoichiometry s *
      operationalRationalDerivative s rates x).map (Rat.castHom ℝ))
    (θ : Fin 21 → ℝ) (w : Fin 9 → ℝ) :
    operationalReactionJacobian q s θ w = J₀+
      operationalWeightedStoichiometry (fun i => (s i : ℝ)) *
        (Matrix.of fun a j => (operationalDerivativeDifferenceExpression q s rates x a j).eval
          (operationalInput θ w)) := by
  let E : Matrix (Fin 18) (Fin 9) ℝ := Matrix.of fun a j => operationalReactionDerivative θ
    (operationalSpecies (fun i => (q i : ℝ)) (fun i => (s i : ℝ)) θ w)
    (fun i j => (operationalSpeciesLinear s i j : ℝ)) a j
  let E₀ := (operationalRationalDerivative s rates x).map (Rat.castHom ℝ)
  have hD : (Matrix.of fun a j => (operationalDerivativeDifferenceExpression q s rates x a j).eval
      (operationalInput θ w)) = E-E₀ := by
    ext a j
    change (operationalDerivativeDifferenceExpression q s rates x a j).eval
      (operationalInput θ w) = (E-E₀) a j
    rw [operationalDerivativeDifferenceExpression_eval]
    rfl
  rw [hD, hJ₀, Matrix.map_mul, ← operationalWeightedStoichiometry_eq_rational_cast]
  change operationalWeightedStoichiometry (fun i => (s i : ℝ))*E =
    operationalWeightedStoichiometry (fun i => (s i : ℝ))*E₀ +
      operationalWeightedStoichiometry (fun i => (s i : ℝ))*(E-E₀)
  rw [Matrix.mul_sub]
  abel

end
end PhosphorylationStableCapacity

namespace PhosphorylationStableCapacity
noncomputable section
open Matrix
open scoped BigOperators

def operationalContractionExpressions (C : Matrix (Fin 9) (Fin 18) ℚ)
    (q s : Fin 9 → ℚ) (rates : Fin 18 → ℚ) (x : Fin 12 → ℚ) :
    Fin 9 → Fin 9 → RationalExpression (Fin 30) := fun i j =>
  RationalExpression.linearCombination 18 (C i)
    (fun a => operationalDerivativeDifferenceExpression q s rates x a j)

def operationalCentreShiftExpressions (C : Matrix (Fin 9) (Fin 18) ℚ)
    (q : Fin 9 → ℚ) (rates : Fin 18 → ℚ) (x : Fin 12 → ℚ) :
    Fin 9 → RationalExpression (Fin 30) := fun i =>
  RationalExpression.linearCombination 18 (C i)
    (operationalFluxDifferenceExpression q rates x)

def operationalLyapunovLossExpressions (C : Matrix (Fin 9) (Fin 18) ℚ)
    (q s : Fin 9 → ℚ) (rates : Fin 18 → ℚ) (x : Fin 12 → ℚ) :
    Fin 9 → Fin 9 → RationalExpression (Fin 30) := fun i j =>
  RationalExpression.linearCombination 18 (fun _ => 1) (fun a =>
    .neg (.add
      (.mul (.const (C i a)) (operationalDerivativeDifferenceExpression q s rates x a j))
      (.mul (.const (C j a)) (operationalDerivativeDifferenceExpression q s rates x a i))))

theorem operationalLyapunovLossExpressions_eval
    (C : Matrix (Fin 9) (Fin 18) ℚ) (q s : Fin 9 → ℚ)
    (rates : Fin 18 → ℚ) (x : Fin 12 → ℚ) (θ : Fin 21 → ℝ) (w : Fin 9 → ℝ) :
    (fun i j => (operationalLyapunovLossExpressions C q s rates x i j).eval
      (operationalInput θ w)) =
    -(C.map (Rat.castHom ℝ) *
        (Matrix.of fun a j => (operationalDerivativeDifferenceExpression q s rates x a j).eval
          (operationalInput θ w)) +
      (C.map (Rat.castHom ℝ) *
        (Matrix.of fun a j => (operationalDerivativeDifferenceExpression q s rates x a j).eval
          (operationalInput θ w))).transpose) := by
  ext i j
  simp only [operationalLyapunovLossExpressions,
    RationalExpression.eval_linearCombination, RationalExpression.eval,
    Rat.cast_one, one_mul, Matrix.neg_apply, Matrix.add_apply,
    Matrix.transpose_apply, Matrix.mul_apply, Matrix.map_apply, Matrix.of_apply,
    Rat.coe_castHom]
  rw [Finset.sum_neg_distrib, Finset.sum_add_distrib]

/-- A rational interval loss certificate gives dissipation of the actual
nonlinear field's Jacobian with one common fixed Lyapunov matrix. -/
theorem operational_actual_lyapunov_dissipation
    (C : Matrix (Fin 9) (Fin 18) ℚ) (q s : Fin 9 → ℚ)
    (rates : Fin 18 → ℚ) (x : Fin 12 → ℚ)
    (J₀ P Q : Matrix (Fin 9) (Fin 9) ℝ) (hP : P.IsSymm)
    (hC : C.map (Rat.castHom ℝ) =
      P * operationalWeightedStoichiometry (fun i => (s i : ℝ)))
    (hJ₀ : J₀ = (operationalRationalStoichiometry s *
      operationalRationalDerivative s rates x).map (Rat.castHom ℝ))
    (hQ : J₀.transpose*P+P*J₀ = -Q)
    (c₀ : ℝ) (hcoercivity : ∀ v : Fin 9 → ℝ,
      c₀*(∑ i, v i^2) ≤ v ⬝ᵥ (Q *ᵥ v))
    (I : Fin 30 → RationalInterval) (loss : ℚ)
    (hcheck : ∀ i, (∑ j, (((operationalLyapunovLossExpressions C q s rates x i j).enclose I).magnitude)) ≤ loss)
    (θ : Fin 21 → ℝ) (w : Fin 9 → ℝ)
    (hinput : ∀ i, (I i).Contains (operationalInput θ w i)) (v : Fin 9 → ℝ) :
    2*(v ⬝ᵥ (P *ᵥ (operationalReactionJacobian q s θ w *ᵥ v))) ≤
      -(c₀-(loss : ℝ))*(∑ i, v i^2) := by
  let D : Matrix (Fin 18) (Fin 9) ℝ := Matrix.of fun a j =>
    (operationalDerivativeDifferenceExpression q s rates x a j).eval (operationalInput θ w)
  let Δ : Matrix (Fin 9) (Fin 9) ℝ :=
    C.map (Rat.castHom ℝ)*D+(C.map (Rat.castHom ℝ)*D).transpose
  have hΔ : Δ.IsSymm := by
    change (C.map (Rat.castHom ℝ)*D+(C.map (Rat.castHom ℝ)*D).transpose).transpose = _
    rw [Matrix.transpose_add, Matrix.transpose_transpose, add_comm]
  have hEq : (operationalReactionJacobian q s θ w).transpose*P+
      P*operationalReactionJacobian q s θ w = -Q+Δ :=
    precontracted_lyapunov_loss P (operationalReactionJacobian q s θ w) J₀ Q
      (operationalWeightedStoichiometry (fun i => (s i : ℝ)))
      (C.map (Rat.castHom ℝ)) D hP hC
      (operationalReactionJacobian_perturbation q s rates x J₀ hJ₀ θ w) hQ
  have hLoss : (fun i j => (operationalLyapunovLossExpressions C q s rates x i j).eval
      (operationalInput θ w)) = -Δ := operationalLyapunovLossExpressions_eval C q s rates x θ w
  have hrows (i : Fin 9) : (∑ j, |Δ i j|) ≤ (loss : ℝ) := by
    have h := rational_expression_row_bound_of_certificate I
      (operationalLyapunovLossExpressions C q s rates x) loss hcheck
      (operationalInput θ w) hinput i
    change (∑ j, |(fun i j => (operationalLyapunovLossExpressions C q s rates x i j).eval
      (operationalInput θ w)) i j|) ≤ (loss : ℝ) at h
    rw [hLoss] at h
    simpa only [Matrix.neg_apply, abs_neg] using h
  exact lyapunov_directional_le_of_row_loss (operationalReactionJacobian q s θ w)
    P Q Δ hP hΔ c₀ loss hEq hcoercivity hrows v

theorem operationalCentreShiftExpressions_eval
    (C : Matrix (Fin 9) (Fin 18) ℚ) (q s : Fin 9 → ℚ)
    (rates : Fin 18 → ℚ) (x : Fin 12 → ℚ) (θ : Fin 21 → ℝ) (w : Fin 9 → ℝ) :
    (fun i => (operationalCentreShiftExpressions C q rates x i).eval
      (operationalInput θ w)) =
    C.map (Rat.castHom ℝ) *ᵥ
      (operationalReactionFlux θ
        (operationalSpecies (fun i => (q i : ℝ)) (fun i => (s i : ℝ)) θ 0) -
        fun a => (operationalNominalFlux rates x a : ℝ)) := by
  ext i
  simp only [operationalCentreShiftExpressions,
    RationalExpression.eval_linearCombination]
  simp_rw [operationalFluxDifferenceExpression_eval q s rates x θ w]
  rfl

theorem operational_actual_centre_residual_bound
    (C : Matrix (Fin 9) (Fin 18) ℚ) (q s : Fin 9 → ℚ)
    (rates : Fin 18 → ℚ) (x : Fin 12 → ℚ) (R : Matrix (Fin 9) (Fin 9) ℝ)
    (hC : C.map (Rat.castHom ℝ) =
      R * operationalWeightedStoichiometry (fun i => (s i : ℝ)))
    (hbalanced : operationalWeightedStoichiometry (fun i => (s i : ℝ)) *ᵥ
      (fun a => (operationalNominalFlux rates x a : ℝ)) = 0)
    (I : Fin 30 → RationalInterval) (S : ℚ) (hS : 0 ≤ S)
    (hcheck : ∀ i, (((operationalCentreShiftExpressions C q rates x i).enclose I).magnitude) ≤ S)
    (θ : Fin 21 → ℝ)
    (hinput : ∀ i, (I i).Contains (operationalInput θ 0 i)) :
    ‖matrixSupContinuousMap R
      (operationalWeightedField (fun i => (q i : ℝ)) (fun i => (s i : ℝ)) θ 0)‖ ≤
      (S : ℝ) := by
  let flux := operationalReactionFlux θ
    (operationalSpecies (fun i => (q i : ℝ)) (fun i => (s i : ℝ)) θ 0)
  let nominal : Fin 18 → ℝ := fun a => (operationalNominalFlux rates x a : ℝ)
  have hfield : operationalWeightedField (fun i => (q i : ℝ))
      (fun i => (s i : ℝ)) θ 0 =
      operationalWeightedStoichiometry (fun i => (s i : ℝ)) *ᵥ flux := by
    ext i
    exact operationalWeightedField_reaction_sum _ _ θ 0 i
  have hzero : C.map (Rat.castHom ℝ) *ᵥ nominal = 0 := by
    rw [hC, ← Matrix.mulVec_mulVec, hbalanced, Matrix.mulVec_zero]
  have heval : matrixSupContinuousMap R
      (operationalWeightedField (fun i => (q i : ℝ)) (fun i => (s i : ℝ)) θ 0) =
      (fun i => (operationalCentreShiftExpressions C q rates x i).eval
        (operationalInput θ 0)) := by
    rw [matrixSupContinuousMap_apply, hfield,
      Matrix.mulVec_mulVec, ← hC,
      operationalCentreShiftExpressions_eval C q s rates x θ 0,
      Matrix.mulVec_sub, hzero, sub_zero]
  rw [heval]
  apply (pi_norm_le_iff_of_nonneg (Rat.cast_nonneg.mpr hS)).mpr
  intro i
  rw [Real.norm_eq_abs]
  exact (RationalExpression.abs_eval_le I (operationalInput θ 0) hinput
    (operationalCentreShiftExpressions C q rates x i)).trans (Rat.cast_le.mpr (hcheck i))

theorem operationalContractionExpressions_eval
    (C : Matrix (Fin 9) (Fin 18) ℚ) (q s : Fin 9 → ℚ)
    (rates : Fin 18 → ℚ) (x : Fin 12 → ℚ) (θ : Fin 21 → ℝ) (w : Fin 9 → ℝ) :
    (fun i j => (operationalContractionExpressions C q s rates x i j).eval
      (operationalInput θ w)) =
    C.map (Rat.castHom ℝ) *
      (Matrix.of fun a j => (operationalDerivativeDifferenceExpression q s rates x a j).eval
        (operationalInput θ w)) := by
  ext i j
  simp only [operationalContractionExpressions,
    RationalExpression.eval_linearCombination, Matrix.mul_apply, Matrix.map_apply,
    Matrix.of_apply, Rat.coe_castHom]

/-- Kernel-checked rational rows bound the true derivative of the
preconditioned physical field, uniformly throughout the independent box. -/
theorem operational_actual_newton_derivative_bound
    (C : Matrix (Fin 9) (Fin 18) ℚ) (q s : Fin 9 → ℚ)
    (rates : Fin 18 → ℚ) (x : Fin 12 → ℚ)
    (R J₀ : Matrix (Fin 9) (Fin 9) ℝ)
    (hC : C.map (Rat.castHom ℝ) =
      R * operationalWeightedStoichiometry (fun i => (s i : ℝ)))
    (hR : R*J₀ = 1)
    (hJ₀ : J₀ = (operationalRationalStoichiometry s *
      operationalRationalDerivative s rates x).map (Rat.castHom ℝ))
    (I : Fin 30 → RationalInterval) (B : ℚ) (hB : 0 ≤ B)
    (hcheck : ∀ i, (∑ j, (((operationalContractionExpressions C q s rates x i j).enclose I).magnitude)) ≤ B)
    (θ : Fin 21 → ℝ) (w : Fin 9 → ℝ)
    (hinput : ∀ i, (I i).Contains (operationalInput θ w i)) :
    ‖ContinuousLinearMap.id ℝ (Fin 9 → ℝ) -
      (matrixSupContinuousMap R).comp
        (fderiv ℝ (operationalWeightedField (fun i => (q i : ℝ))
          (fun i => (s i : ℝ)) θ) w)‖ ≤ (B : ℝ) := by
  rw [(operationalWeightedField_hasFDerivAt (fun i => (q i : ℝ))
    (fun i => (s i : ℝ)) θ w).fderiv]
  apply matrixSupContinuousMap_newton_defect_norm R
    (operationalReactionJacobian q s θ w) _
    (operationalReactionJacobian_action q s θ w) (B : ℝ) (Rat.cast_nonneg.mpr hB)
  have hdefect := precontracted_newton_defect R
    (operationalReactionJacobian q s θ w) J₀
    (operationalWeightedStoichiometry (fun i => (s i : ℝ)))
    (C.map (Rat.castHom ℝ))
    (Matrix.of fun a j => (operationalDerivativeDifferenceExpression q s rates x a j).eval
      (operationalInput θ w)) hC hR
    (operationalReactionJacobian_perturbation q s rates x J₀ hJ₀ θ w)
  rw [hdefect, ← operationalContractionExpressions_eval]
  intro i
  change (∑ j : Fin 9, |-(operationalContractionExpressions C q s rates x i j).eval
    (operationalInput θ w)|) ≤ (B : ℝ)
  simpa only [abs_neg] using
    rational_expression_row_bound_of_certificate I
      (operationalContractionExpressions C q s rates x) B hcheck
      (operationalInput θ w) hinput i

theorem operational_actual_species_positive
    (q s : Fin 9 → ℚ) (I : Fin 30 → RationalInterval)
    (hcheck : ∀ i : Fin 12, 0 < ((operationalSpeciesExpression q s i).enclose I).lo)
    (θ : Fin 21 → ℝ) (w : Fin 9 → ℝ)
    (hinput : ∀ i, (I i).Contains (operationalInput θ w i)) (i : Fin 12) :
    0 < operationalSpecies (fun j => (q j : ℝ)) (fun j => (s j : ℝ)) θ w i := by
  have h := RationalExpression.eval_mem_enclose I (operationalInput θ w)
    hinput (operationalSpeciesExpression q s i)
  rw [operationalSpeciesExpression_eval] at h
  exact (Rat.cast_pos.mpr (hcheck i)).trans_le h.1

end
end PhosphorylationStableCapacity

namespace PhosphorylationStableCapacity
noncomputable section
open PhosphorylationSharpness

/-- The reconstructed state in micromolar units. -/
def operationalPhysicalState (q s : Fin 9 → ℝ) (θ : Fin 21 → ℝ)
    (w : Fin 9 → ℝ) : State 3 :=
  let φ := operationalPhysicalParameters θ
  unChart (φ 18) (φ 19) (φ 20)
    (ofCoordinateSpace (operationalUnpack (fun i => q i/10)+
      operationalLift (fun i => s i/10) w))

theorem operationalPhysicalState_positive
    (q s : Fin 9 → ℝ) (θ : Fin 21 → ℝ) (w : Fin 9 → ℝ)
    (hpositive : ∀ i, 0 < operationalSpecies q s θ w i) :
    (operationalPhysicalState q s θ w).Positive := by
  apply operationalSpecies_positive_state
  rw [operational_physical_species]
  intro i
  exact div_pos (hpositive i) (by norm_num)

theorem operationalPhysicalState_equilibrium
    (q s : Fin 9 → ℝ) (hs : ∀ i, s i ≠ 0) (θ : Fin 21 → ℝ)
    (w : Fin 9 → ℝ) (heq : operationalWeightedField q s θ w = 0) :
    Equilibrium (operationalParameterRates (operationalPhysicalParameters θ))
      (operationalPhysicalState q s θ w) := by
  apply (operationalWeightedField_zero_iff_equilibrium _ _
    (fun i => div_ne_zero (hs i) (by norm_num)) _ w).mp
  rw [operational_physical_weighted_field q s hs θ w, heq, smul_zero]

/-- Reconstruction fixes all three physical totals for every weighted point. -/
theorem operationalPhysicalState_inClass
    (q s : Fin 9 → ℝ) (θ : Fin 21 → ℝ) (w : Fin 9 → ℝ) :
    InClass (operationalPhysicalParameters θ 18)
      (operationalPhysicalParameters θ 19) (operationalPhysicalParameters θ 20)
      (operationalPhysicalState q s θ w) := by
  exact unChart_inClass _ _ _ _

/-- The paper's micromolar readout is C₀=0.1 times the literal fully
phosphorylated free substrate plus its phosphatase complex. -/
def operationalPhysicalReadout (q s : Fin 9 → ℝ) (θ : Fin 21 → ℝ)
    (w : Fin 9 → ℝ) : ℝ :=
  let x := unChart (θ 18) (θ 19) (θ 20)
    (ofCoordinateSpace (operationalUnpack q+operationalLift s w))
  (1/10 : ℝ)*(x.S 3+x.D 2)

theorem operationalPhysicalReadout_eq (q s : Fin 9 → ℝ)
    (θ : Fin 21 → ℝ) (w : Fin 9 → ℝ) :
    operationalPhysicalReadout q s θ w =
      (1/10 : ℝ)*(q 2+q 8+s 2*w 2+s 8*w 8) := by
  change (1/10 : ℝ)*((q 2+s 2*w 2)+(q 8+s 8*w 8)) = _
  ring

/-- The micromolar readout is the literal concentration sum in the converted
physical state, with the same independently perturbed parameters. -/
theorem operationalPhysicalReadout_eq_converted_state
    (q s : Fin 9 → ℝ) (θ : Fin 21 → ℝ) (w : Fin 9 → ℝ) :
    let φ := operationalPhysicalParameters θ
    let x := unChart (φ 18) (φ 19) (φ 20)
      (ofCoordinateSpace (operationalUnpack (fun i => q i/10) +
        operationalLift (fun i => s i/10) w))
    operationalPhysicalReadout q s θ w = x.S 3 + x.D 2 := by
  rw [operationalPhysicalReadout_eq]
  change (1/10 : ℝ)*(q 2+q 8+s 2*w 2+s 8*w 8) =
    (q 2/10+(s 2/10)*w 2)+(q 8/10+(s 8/10)*w 8)
  ring

theorem operationalPhysicalReadout_measurement_bound
    (q s : Fin 9 → ℝ) (hs2 : 0 ≤ s 2) (hs8 : 0 ≤ s 8)
    (θ : Fin 21 → ℝ) (w : Fin 9 → ℝ) (ρ measurement : ℝ)
    (hw : ‖w‖ ≤ ρ/4) (hmeasurement : |measurement| ≤ (1/1000 : ℝ)) :
    |operationalPhysicalReadout q s θ w+measurement-
      (1/10 : ℝ)*(q 2+q 8)| ≤
      (1/10 : ℝ)*(s 2+s 8)*(ρ/4)+(1/1000 : ℝ) := by
  have hlinear : operationalPhysicalReadout q s θ w+measurement-
      (1/10 : ℝ)*(q 2+q 8) =
      (1/10 : ℝ)*(s 2*w 2+s 8*w 8)+measurement := by
    rw [operationalPhysicalReadout_eq]
    ring
  rw [hlinear]
  have h2 : |w 2| ≤ ρ/4 := by
    simpa only [Real.norm_eq_abs] using (norm_le_pi_norm w 2).trans hw
  have h8 : |w 8| ≤ ρ/4 := by
    simpa only [Real.norm_eq_abs] using (norm_le_pi_norm w 8).trans hw
  exact two_coordinate_readout_error_bound (s 2) (s 8) (1/10) (ρ/4)
    (1/1000) (w 2) (w 8) measurement hs2 hs8 (by norm_num) h2 h8 hmeasurement

end
end PhosphorylationStableCapacity

namespace PhosphorylationStableCapacity
noncomputable section
open Matrix PhosphorylationSharpness
open scoped BigOperators

/-- The independent interval certificates imply a unique positive equilibrium
of the literal three-site mass-action system, with the printed quarter-radius
shift. The same parameters occur in every certificate and physical state. -/
theorem operational_certified_positive_equilibrium
    (C : Matrix (Fin 9) (Fin 18) ℚ) (q s : Fin 9 → ℚ)
    (rates : Fin 18 → ℚ) (x : Fin 12 → ℚ)
    (R J₀ : Matrix (Fin 9) (Fin 9) ℝ)
    (hs : ∀ i, s i ≠ 0)
    (hC : C.map (Rat.castHom ℝ) =
      R * operationalWeightedStoichiometry (fun i => (s i : ℝ)))
    (hR : J₀*R = 1)
    (hJ₀ : J₀ = (operationalRationalStoichiometry s *
      operationalRationalDerivative s rates x).map (Rat.castHom ℝ))
    (hbalanced : operationalWeightedStoichiometry (fun i => (s i : ℝ)) *ᵥ
      (fun a => (operationalNominalFlux rates x a : ℝ)) = 0)
    (I : Fin 30 → RationalInterval) (ρ S : ℚ) (hρ : 0 < ρ) (hS : 0 ≤ S)
    (hsmall : S ≤ 3*ρ/16)
    (hcontraction : ∀ i, (∑ j,
      ((operationalContractionExpressions C q s rates x i j).enclose I).magnitude) ≤ 1/4)
    (hshift : ∀ i,
      ((operationalCentreShiftExpressions C q rates x i).enclose I).magnitude ≤ S)
    (hpositive : ∀ i : Fin 12,
      0 < ((operationalSpeciesExpression q s i).enclose I).lo)
    (θ : Fin 21 → ℝ)
    (hinput : ∀ w : Fin 9 → ℝ, ‖w‖ ≤ (ρ : ℝ) → ∀ i,
      (I i).Contains (operationalInput θ w i)) :
    ∃ w : Fin 9 → ℝ, ‖w‖ ≤ (ρ : ℝ)/4 ∧
      (unChart (θ 18) (θ 19) (θ 20)
        (ofCoordinateSpace (operationalUnpack (fun i => (q i : ℝ))+
          operationalLift (fun i => (s i : ℝ)) w))).Positive ∧
      Equilibrium (operationalParameterRates θ)
        (unChart (θ 18) (θ 19) (θ 20)
          (ofCoordinateSpace (operationalUnpack (fun i => (q i : ℝ))+
            operationalLift (fun i => (s i : ℝ)) w))) ∧
      ∀ v : Fin 9 → ℝ, ‖v‖ ≤ (ρ : ℝ) →
        operationalWeightedField (fun i => (q i : ℝ))
          (fun i => (s i : ℝ)) θ v = 0 → v = w := by
  have hρreal : (0 : ℝ) < ρ := Rat.cast_pos.mpr hρ
  have hRleft : R*J₀ = 1 := mul_eq_one_comm.mp hR
  have hder (w : Fin 9 → ℝ) (hw : w ∈ Metric.closedBall 0 (ρ : ℝ)) :=
    operational_actual_newton_derivative_bound C q s rates x R J₀
      hC hRleft hJ₀ I (1/4) (by norm_num) hcontraction θ w
      (hinput w (by simpa only [Metric.mem_closedBall, dist_zero_right] using hw))
  have hzeroInput := hinput 0 (by simpa using hρreal.le)
  have hcentre := operational_actual_centre_residual_bound C q s rates x R
    hC hbalanced I S hS hshift θ hzeroInput
  have hsmallReal : (S : ℝ) ≤ 3*(ρ : ℝ)/16 := by exact_mod_cast hsmall
  obtain ⟨w, hw, heq, hquarter, hunique⟩ :=
    unique_zero_in_closedBall_of_preconditioned_contraction
      (operationalWeightedField (fun i => (q i : ℝ)) (fun i => (s i : ℝ)) θ)
      (matrixSupContinuousMap R)
      (matrixSupContinuousMap_injective_of_left_inverse J₀ R hR) 0
      (ρ : ℝ) hρreal (1/4) (by norm_num)
      (fun v _hv => (operationalWeightedField_hasFDerivAt _ _ θ v).differentiableAt)
      (by intro v hv; simpa only [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat,
        NNReal.coe_div, NNReal.coe_one, NNReal.coe_ofNat] using hder v hv)
      (by norm_num only [NNReal.coe_div, NNReal.coe_one, NNReal.coe_ofNat];
               linarith only [hcentre, hsmallReal])
  have hwNorm : ‖w‖ ≤ (ρ : ℝ) := by
    simpa only [Metric.mem_closedBall, dist_zero_right] using hw
  refine ⟨w, ?_, ?_, ?_, ?_⟩
  · simpa only [dist_zero_right] using hquarter
  · exact operationalSpecies_positive_state _ _ θ w
      (operational_actual_species_positive q s I hpositive θ w (hinput w hwNorm))
  · exact (operationalWeightedField_zero_iff_equilibrium _ _
      (fun i => Rat.cast_ne_zero.mpr (hs i)) θ w).mp heq
  · intro v hv he
    exact hunique v (by simpa only [Metric.mem_closedBall, dist_zero_right] using hv) he

end
end PhosphorylationStableCapacity

namespace PhosphorylationStableCapacity
noncomputable section
open Matrix PhosphorylationSharpness Set
open scoped BigOperators

/-- Fixed common Lyapunov certificates yield an existing physical forward
solution and the operational recovery conclusions. The field and Jacobian
are the actual weighted mass-action system, at one common parameter vector. -/
theorem operational_certified_forward_recovery
    (q s : Fin 9 → ℚ) (hs : ∀ i, s i ≠ 0)
    (θ : Fin 21 → ℝ) (hθ : ∀ i, 0 < θ i)
    (P : Matrix (Fin 9) (Fin 9) ℝ) (hP : P.IsSymm)
    (equilibrium initial : Fin 9 → ℝ) (ρ ρin p c M : ℝ)
    (hρ : 0 < ρ) (hρin : 0 ≤ ρin) (hinner : ρin ≤ ρ/2)
    (hp : 0 < p) (hc : 0 < c) (hM : 0 < M)
    (hshift : ‖equilibrium‖ ≤ ρ/4)
    (heq : operationalWeightedField (fun i => (q i : ℝ))
      (fun i => (s i : ℝ)) θ equilibrium = 0)
    (hpositive : ∀ w : Fin 9 → ℝ, ‖w‖ ≤ ρ →
      ∀ i, 0 < operationalSpecies (fun i => (q i : ℝ))
        (fun i => (s i : ℝ)) θ w i)
    (hlower : ∀ v : Fin 9 → ℝ,
      p*(∑ i, v i^2) ≤ v ⬝ᵥ (P *ᵥ v))
    (hupper : ∀ v : Fin 9 → ℝ,
      v ⬝ᵥ (P *ᵥ v) ≤ M*(∑ i, v i^2))
    (hdiss : ∀ w : Fin 9 → ℝ, ‖w‖ ≤ ρ → ∀ v : Fin 9 → ℝ,
      2*(v ⬝ᵥ (P *ᵥ (operationalReactionJacobian q s θ w *ᵥ v))) ≤
        -c*(∑ i, v i^2))
    (hmargin : M*ρin^2 < p*(ρ/2)^2)
    (hinit : (∑ i, (initial i-equilibrium i)^2) ≤ ρin^2) :
    (∃ γ : ℝ → Fin 9 → ℝ,
      IsOperationalForwardCurve (fun i => (q i : ℝ))
        (fun i => (s i : ℝ)) θ initial γ) ∧
    ∀ γ : ℝ → Fin 9 → ℝ,
      IsOperationalForwardCurve (fun i => (q i : ℝ))
        (fun i => (s i : ℝ)) θ initial γ →
      (∀ t : ℝ, 0 ≤ t → ‖γ t‖ < ρ) ∧
      (∀ t : ℝ, 0 ≤ t → finiteEuclideanLength (γ t-equilibrium) ≤
        (ρ/2)*Real.exp (-(c/(2*M))*t)) ∧
      (∀ t : ℝ, 6*M/c ≤ t →
        finiteEuclideanLength (γ t-equilibrium) < ρ/20) := by
  have hdist : ‖initial-equilibrium‖ ≤ ρin :=
    (sup_norm_le_finiteEuclideanLength (initial-equilibrium)).trans
      (Real.sqrt_le_iff.mpr ⟨hρin, hinit⟩)
  have hinitial : ‖initial‖ ≤ ρ := by
    have hi : initial = (initial-equilibrium)+equilibrium := by abel
    rw [hi]
    have hn := norm_add_le (initial-equilibrium) equilibrium
    linarith only [hn, hdist, hshift, hinner, hρ]
  have hx := operationalSpecies_positive_state _ _ θ initial
    (hpositive initial hinitial)
  have hpoly : operationalUnpack (fun i => (q i : ℝ))+
      operationalLift (fun i => (s i : ℝ)) initial ∈
        classPolytope 3 (θ 18) (θ 19) (θ 20) := by
    apply (mem_classPolytope_iff_nonnegative _ _ _ _).mpr
    exact ⟨fun i => (hx.1 i).le, hx.2.1.le, hx.2.2.1.le,
      fun i => (hx.2.2.2.1 i).le, fun i => (hx.2.2.2.2 i).le⟩
  obtain ⟨γ, hγ⟩ := exists_operational_forward_curve _ _
    (fun i => Rat.cast_ne_zero.mpr (hs i)) θ (hθ 18)
    (operationalParameterRates_positive θ hθ) initial hpoly
  refine ⟨⟨γ, hγ⟩, ?_⟩
  intro β hβ
  obtain ⟨hstay, henv, htime⟩ := certified_quadratic_recovery
    (operationalWeightedField (fun i => (q i : ℝ)) (fun i => (s i : ℝ)) θ)
    (operationalReactionJacobian q s θ) P hP 0 equilibrium ρ ρin p c M
    hρ hp hc hM (by simpa only [sub_zero] using hshift) heq hlower hupper
    (operationalReactionJacobian_midpoint q s θ)
    (fun w hw => hdiss w (by simpa only [sub_zero] using hw)) hmargin β
    (operationalForwardCurve_coordinate_derivative _ _ θ initial β hβ)
    (by simpa only [hβ.1] using hinit)
  exact ⟨by simpa only [sub_zero] using hstay, henv, htime⟩

end
end PhosphorylationStableCapacity

namespace PhosphorylationStableCapacity
noncomputable section

/-- The manuscript fixes T₀=10 seconds. This clock conversion carries the
model-time recovery certificate to exactly the printed physical-time bound. -/
theorem operational_recovery_physical_clock
    (γ : ℝ → Fin 9 → ℝ) (equilibrium : Fin 9 → ℝ)
    (ρ c M : ℝ)
    (henvelope : ∀ t : ℝ, 0 ≤ t →
      finiteEuclideanLength (γ t-equilibrium) ≤
        (ρ/2)*Real.exp (-(c/(2*M))*t))
    (hrecovery : ∀ t : ℝ, 6*M/c ≤ t →
      finiteEuclideanLength (γ t-equilibrium) < ρ/20) :
    (∀ t : ℝ, 0 ≤ t → finiteEuclideanLength (γ (t/10)-equilibrium) ≤
      (ρ/2)*Real.exp (-(c/(2*M))*(t/10))) ∧
    (∀ t : ℝ, 60*M/c ≤ t →
      finiteEuclideanLength (γ (t/10)-equilibrium) < ρ/20) := by
  refine ⟨fun t ht => henvelope (t/10) (div_nonneg ht (by norm_num)), ?_⟩
  intro t ht
  apply hrecovery (t/10)
  have hscale : 60*M/c/10 = 6*M/c := by ring
  rw [← hscale]
  exact div_le_div_of_nonneg_right ht (by norm_num)

end
end PhosphorylationStableCapacity

namespace PhosphorylationStableCapacity
noncomputable section
open Matrix PhosphorylationSharpness Set
open scoped BigOperators

theorem operational_certified_closed_ellipsoid
    (q s : Fin 9 → ℚ) (θ : Fin 21 → ℝ)
    (P : Matrix (Fin 9) (Fin 9) ℝ) (hP : P.IsSymm)
    (equilibrium : Fin 9 → ℝ) (ρ p c M : ℝ)
    (hρ : 0 < ρ) (hp : 0 < p) (hc : 0 < c) (hM : 0 < M)
    (hshift : ‖equilibrium‖ ≤ ρ/4)
    (heq : operationalWeightedField (fun i => (q i : ℝ))
      (fun i => (s i : ℝ)) θ equilibrium = 0)
    (hlower : ∀ v : Fin 9 → ℝ,
      p*(∑ i, v i^2) ≤ v ⬝ᵥ (P *ᵥ v))
    (hupper : ∀ v : Fin 9 → ℝ,
      v ⬝ᵥ (P *ᵥ v) ≤ M*(∑ i, v i^2))
    (hdiss : ∀ w : Fin 9 → ℝ, ‖w‖ ≤ ρ → ∀ v : Fin 9 → ℝ,
      2*(v ⬝ᵥ (P *ᵥ (operationalReactionJacobian q s θ w *ᵥ v))) ≤
        -c*(∑ i, v i^2))
    (initial : Fin 9 → ℝ) (γ : ℝ → Fin 9 → ℝ)
    (hγ : IsOperationalForwardCurve (fun i => (q i : ℝ))
      (fun i => (s i : ℝ)) θ initial γ)
    (hinit : (initial-equilibrium) ⬝ᵥ (P *ᵥ (initial-equilibrium)) ≤ p*(ρ/2)^2) :
    (∀ t : ℝ, 0 ≤ t →
      (γ t-equilibrium) ⬝ᵥ (P *ᵥ (γ t-equilibrium)) ≤ p*(ρ/2)^2) ∧
    (∀ t : ℝ, 0 ≤ t → ‖γ t‖ < ρ) ∧
    (∀ t : ℝ, 0 ≤ t → finiteEuclideanLength (γ t-equilibrium) ≤
      (ρ/2)*Real.exp (-(c/(2*M))*t)) ∧
    (∀ t : ℝ, 6*M/c ≤ t → finiteEuclideanLength (γ t-equilibrium) < ρ/20) := by
  obtain ⟨henergy, hstay, henv, htime⟩ := certified_closed_quadratic_recovery
    (operationalWeightedField (fun i => (q i : ℝ)) (fun i => (s i : ℝ)) θ)
    (operationalReactionJacobian q s θ) P hP 0 equilibrium ρ p c M
    hρ hp hc hM (by simpa only [sub_zero] using hshift) heq hlower hupper
    (operationalReactionJacobian_midpoint q s θ)
    (fun w hw => hdiss w (by simpa only [sub_zero] using hw)) γ
    (operationalForwardCurve_coordinate_derivative _ _ θ initial γ hγ)
    (by simpa only [hγ.1] using hinit)
  exact ⟨henergy, by simpa only [sub_zero] using hstay, henv, htime⟩

/-- The recovery certificate controls every solution of the actual physical
equation in seconds, by converting that solution back to model time. -/
theorem operational_physical_recovery_of_model_certificate
    (q s : Fin 9 → ℝ) (θ : Fin 21 → ℝ) (initial equilibrium : Fin 9 → ℝ)
    (ρ c M : ℝ)
    (hcertificate : ∀ β : ℝ → Fin 9 → ℝ,
      IsOperationalForwardCurve q s θ initial β →
      (∀ t : ℝ, 0 ≤ t → ‖β t‖ < ρ) ∧
      (∀ t : ℝ, 0 ≤ t → finiteEuclideanLength (β t-equilibrium) ≤
        (ρ/2)*Real.exp (-(c/(2*M))*t)) ∧
      (∀ t : ℝ, 6*M/c ≤ t → finiteEuclideanLength (β t-equilibrium) < ρ/20)) :
    ∀ γ : ℝ → Fin 9 → ℝ, IsOperationalPhysicalCurve q s θ initial γ →
      (∀ t : ℝ, 0 ≤ t → ‖γ t‖ < ρ) ∧
      (∀ t : ℝ, 0 ≤ t → finiteEuclideanLength (γ t-equilibrium) ≤
        (ρ/2)*Real.exp (-(c/(2*M))*(t/10))) ∧
      (∀ t : ℝ, 60*M/c ≤ t → finiteEuclideanLength (γ t-equilibrium) < ρ/20) := by
  intro γ hγ
  obtain ⟨hstay, henv, htime⟩ := hcertificate (fun t => γ (10*t))
    (operational_model_curve_of_physical q s θ initial γ hγ)
  obtain ⟨henvSeconds, htimeSeconds⟩ := operational_recovery_physical_clock
    (fun t => γ (10*t)) equilibrium ρ c M henv htime
  have hclock (t : ℝ) : (10 : ℝ)*(t/10) = t := by ring
  refine ⟨?_, ?_, ?_⟩
  · intro t ht
    simpa only [hclock] using hstay (t/10) (div_nonneg ht (by norm_num))
  · intro t ht
    simpa only [hclock] using henvSeconds t ht
  · intro t ht
    simpa only [hclock] using htimeSeconds t ht

theorem operational_exists_physical_forward_curve
    (q s : Fin 9 → ℚ) (hs : ∀ i, s i ≠ 0)
    (θ : Fin 21 → ℝ) (hθ : ∀ i, 0 < θ i) (initial : Fin 9 → ℝ)
    (hpositive : ∀ i, 0 < operationalSpecies (fun j => (q j : ℝ))
      (fun j => (s j : ℝ)) θ initial i) :
    ∃ γ : ℝ → Fin 9 → ℝ,
      IsOperationalPhysicalCurve (fun i => (q i : ℝ))
        (fun i => (s i : ℝ)) θ initial γ := by
  have hx := operationalSpecies_positive_state _ _ θ initial hpositive
  have hpoly : operationalUnpack (fun i => (q i : ℝ))+
      operationalLift (fun i => (s i : ℝ)) initial ∈
        classPolytope 3 (θ 18) (θ 19) (θ 20) := by
    apply (mem_classPolytope_iff_nonnegative _ _ _ _).mpr
    exact ⟨fun i => (hx.1 i).le, hx.2.1.le, hx.2.2.1.le,
      fun i => (hx.2.2.2.1 i).le, fun i => (hx.2.2.2.2 i).le⟩
  obtain ⟨γ, hγ⟩ := exists_operational_forward_curve _ _
    (fun i => Rat.cast_ne_zero.mpr (hs i)) θ (hθ 18)
    (operationalParameterRates_positive θ hθ) initial hpoly
  exact ⟨fun t => γ (t/10), operational_physical_curve_of_model _ _ θ initial γ hγ⟩

/-- Every physical solution from the closed ellipsoid, including its boundary,
obeys the fixed-matrix certificate and the recovery bound in seconds. -/
theorem operational_certified_physical_closed_ellipsoid
    (q s : Fin 9 → ℚ) (θ : Fin 21 → ℝ)
    (P : Matrix (Fin 9) (Fin 9) ℝ) (hP : P.IsSymm)
    (equilibrium : Fin 9 → ℝ) (ρ p c M : ℝ)
    (hρ : 0 < ρ) (hp : 0 < p) (hc : 0 < c) (hM : 0 < M)
    (hshift : ‖equilibrium‖ ≤ ρ/4)
    (heq : operationalWeightedField (fun i => (q i : ℝ))
      (fun i => (s i : ℝ)) θ equilibrium = 0)
    (hlower : ∀ v : Fin 9 → ℝ,
      p*(∑ i, v i^2) ≤ v ⬝ᵥ (P *ᵥ v))
    (hupper : ∀ v : Fin 9 → ℝ,
      v ⬝ᵥ (P *ᵥ v) ≤ M*(∑ i, v i^2))
    (hdiss : ∀ w : Fin 9 → ℝ, ‖w‖ ≤ ρ → ∀ v : Fin 9 → ℝ,
      2*(v ⬝ᵥ (P *ᵥ (operationalReactionJacobian q s θ w *ᵥ v))) ≤
        -c*(∑ i, v i^2))
    (initial : Fin 9 → ℝ) (γ : ℝ → Fin 9 → ℝ)
    (hγ : IsOperationalPhysicalCurve (fun i => (q i : ℝ))
      (fun i => (s i : ℝ)) θ initial γ)
    (hinit : (initial-equilibrium) ⬝ᵥ (P *ᵥ (initial-equilibrium)) ≤ p*(ρ/2)^2) :
    (∀ t : ℝ, 0 ≤ t →
      (γ t-equilibrium) ⬝ᵥ (P *ᵥ (γ t-equilibrium)) ≤ p*(ρ/2)^2) ∧
    (∀ t : ℝ, 0 ≤ t → ‖γ t‖ < ρ) ∧
    (∀ t : ℝ, 0 ≤ t → finiteEuclideanLength (γ t-equilibrium) ≤
      (ρ/2)*Real.exp (-(c/(2*M))*(t/10))) ∧
    (∀ t : ℝ, 60*M/c ≤ t → finiteEuclideanLength (γ t-equilibrium) < ρ/20) := by
  obtain ⟨henergy, hstay, henv, htime⟩ := operational_certified_closed_ellipsoid
    q s θ P hP equilibrium ρ p c M hρ hp hc hM hshift heq hlower hupper hdiss
    initial (fun t => γ (10*t))
    (operational_model_curve_of_physical _ _ θ initial γ hγ) hinit
  obtain ⟨henvSeconds, htimeSeconds⟩ := operational_recovery_physical_clock
    (fun t => γ (10*t)) equilibrium ρ c M henv htime
  have hclock (t : ℝ) : (10 : ℝ)*(t/10) = t := by ring
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro t ht
    simpa only [hclock] using henergy (t/10) (div_nonneg ht (by norm_num))
  · intro t ht
    simpa only [hclock] using hstay (t/10) (div_nonneg ht (by norm_num))
  · intro t ht
    simpa only [hclock] using henvSeconds t ht
  · intro t ht
    simpa only [hclock] using htimeSeconds t ht

end
end PhosphorylationStableCapacity
