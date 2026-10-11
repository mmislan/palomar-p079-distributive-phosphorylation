module
public import proofs.PhosphorylationStableCapacity.OperationalCoordinateMaps
public import proofs.PhosphorylationStableCapacity.OperationalAffineExpressions
public import proofs.PhosphorylationStableCapacity.OperationalReactionExpressions
public import proofs.PhosphorylationStableCapacity.FiniteThreeSiteJacobianAction
public import proofs.PhosphorylationStableCapacity.FiniteThreeSiteMidpoint
public import proofs.PhosphorylationStableCapacity.ClassPhysicalForwardFlow
public import Mathlib.Data.Rat.Cast.Lemmas
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.NormNum

@[expose] public section

set_option maxHeartbeats 2000000

namespace PhosphorylationStableCapacity
noncomputable section
open PhosphorylationSharpness

def operationalParameterRates (θ : Fin 21 → ℝ) : Rates 3 where
  a := ![θ 0,θ 6,θ 12]
  b := ![θ 1,θ 7,θ 13]
  c := ![θ 2,θ 8,θ 14]
  alpha := ![θ 3,θ 9,θ 15]
  beta := ![θ 4,θ 10,θ 16]
  gamma := ![θ 5,θ 11,θ 17]

/-- The literal three-site class field in the benchmark's weighted coordinates,
with all18 rates and all3 totals independent. -/
def operationalWeightedField (q s : Fin 9 → ℝ) (θ : Fin 21 → ℝ)
    (w : Fin 9 → ℝ) : Fin 9 → ℝ :=
  operationalRead s (restrictedFieldEuclid (θ 18) (θ 19) (θ 20)
    (operationalParameterRates θ) (operationalUnpack q+operationalLift s w))

def operationalWeightedJacobian (q s : Fin 9 → ℝ) (θ : Fin 21 → ℝ)
    (w : Fin 9 → ℝ) : (Fin 9 → ℝ) →L[ℝ] (Fin 9 → ℝ) :=
  (operationalRead s).comp
    ((restrictedJacobian (θ 18) (θ 19) (θ 20) (operationalParameterRates θ)
      (operationalUnpack q+operationalLift s w)).comp (operationalLift s))

theorem operationalWeightedField_hasFDerivAt (q s : Fin 9 → ℝ)
    (θ : Fin 21 → ℝ) (w : Fin 9 → ℝ) :
    HasFDerivAt (operationalWeightedField q s θ)
      (operationalWeightedJacobian q s θ w) w := by
  have hinput : HasFDerivAt (fun v : Fin 9 → ℝ => operationalUnpack q+operationalLift s v) (operationalLift s) w := (operationalLift s).hasFDerivAt.const_add (operationalUnpack q)
  have hfield : HasFDerivAt
      (restrictedFieldEuclid (θ 18) (θ 19) (θ 20) (operationalParameterRates θ))
      (restrictedJacobian (θ 18) (θ 19) (θ 20) (operationalParameterRates θ)
        (operationalUnpack q+operationalLift s w))
      (operationalUnpack q+operationalLift s w) :=
    (differentiable_restrictedFieldEuclid (θ 18) (θ 19) (θ 20)
      (operationalParameterRates θ) (operationalUnpack q+operationalLift s w)).hasFDerivAt
  have hcomp : HasFDerivAt
      (fun v : Fin 9 → ℝ =>
        restrictedFieldEuclid (θ 18) (θ 19) (θ 20) (operationalParameterRates θ)
          (operationalUnpack q+operationalLift s v))
      ((restrictedJacobian (θ 18) (θ 19) (θ 20) (operationalParameterRates θ)
        (operationalUnpack q+operationalLift s w)).comp (operationalLift s)) w := by
    exact hfield.comp w hinput
  have hcalc : HasFDerivAt
      (fun v : Fin 9 → ℝ => operationalRead s
        (restrictedFieldEuclid (θ 18) (θ 19) (θ 20) (operationalParameterRates θ)
          (operationalUnpack q+operationalLift s v)))
      ((operationalRead s).comp
        ((restrictedJacobian (θ 18) (θ 19) (θ 20) (operationalParameterRates θ)
          (operationalUnpack q+operationalLift s w)).comp (operationalLift s))) w := by
    exact (operationalRead s).hasFDerivAt.comp w hcomp
  exact hcalc

/-- A certified weighted-field zero is an equilibrium of the actual physical
mass-action system reconstructed with the same independently varying totals. -/
theorem operationalWeightedField_zero_iff_equilibrium
    (q s : Fin 9 → ℝ) (hs : ∀ i, s i ≠ 0) (θ : Fin 21 → ℝ) (w : Fin 9 → ℝ) :
    operationalWeightedField q s θ w = 0 ↔
      Equilibrium (operationalParameterRates θ)
        (unChart (θ 18) (θ 19) (θ 20)
          (ofCoordinateSpace (operationalUnpack q+operationalLift s w))) := by
  rw [← restrictedFieldEuclid_eq_zero_iff]
  constructor
  · intro h
    apply operationalRead_injective s hs
    simpa only [operationalWeightedField, map_zero] using h
  · intro h
    simp only [operationalWeightedField, h, map_zero]

end
end PhosphorylationStableCapacity

namespace PhosphorylationStableCapacity
noncomputable section
open PhosphorylationSharpness
open scoped BigOperators

/-- All twelve physical species, reconstructed from the nine weighted class
coordinates and the three independently varying conserved totals. -/
def operationalSpecies (q s : Fin 9 → ℝ) (θ : Fin 21 → ℝ)
    (w : Fin 9 → ℝ) : Fin 12 → ℝ :=
  let u := operationalUnpack q + operationalLift s w
  ![threeSiteFreeS0 (θ 20) u, u.1 0, u.1 1, u.1 2,
    threeSiteFreeE (θ 18) u, threeSiteFreeF (θ 19) u,
    u.2.1 0, u.2.1 1, u.2.1 2, u.2.2 0, u.2.2 1, u.2.2 2]

/-- The eighteen elementary reaction fluxes, in the same order as the eighteen
independent rate parameters. -/
def operationalReactionFlux (θ : Fin 21 → ℝ) (x : Fin 12 → ℝ) : Fin 18 → ℝ :=
  ![θ 0*x 0*x 4, θ 1*x 6, θ 2*x 6,
    θ 3*x 1*x 5, θ 4*x 9, θ 5*x 9,
    θ 6*x 1*x 4, θ 7*x 7, θ 8*x 7,
    θ 9*x 2*x 5, θ 10*x 10, θ 11*x 10,
    θ 12*x 2*x 4, θ 13*x 8, θ 14*x 8,
    θ 15*x 3*x 5, θ 16*x 11, θ 17*x 11]

/-- The literal stoichiometry of the nine unconstrained class coordinates. -/
def operationalStoichiometry : Matrix (Fin 9) (Fin 18) ℚ := Matrix.of
  ![![0,0,1,-1,1,0,-1,1,0,0,0,1,0,0,0,0,0,0],
    ![0,0,0,0,0,0,0,0,1,-1,1,0,-1,1,0,0,0,1],
    ![0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,-1,1,0],
    ![1,-1,-1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
    ![0,0,0,0,0,0,1,-1,-1,0,0,0,0,0,0,0,0,0],
    ![0,0,0,0,0,0,0,0,0,0,0,0,1,-1,-1,0,0,0],
    ![0,0,0,1,-1,-1,0,0,0,0,0,0,0,0,0,0,0,0],
    ![0,0,0,0,0,0,0,0,0,1,-1,-1,0,0,0,0,0,0],
    ![0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,-1,-1]]

/-- The full parameterized mass-action field equals the elementary reaction
sum. This is a physical correspondence theorem for arbitrary real parameters;
the interval checker will subsequently restrict them to the positive box. -/
theorem operationalWeightedField_reaction_sum
    (q s : Fin 9 → ℝ) (θ : Fin 21 → ℝ) (w : Fin 9 → ℝ) (i : Fin 9) :
    operationalWeightedField q s θ w i =
      ∑ a : Fin 18, ((operationalStoichiometry i a : ℝ)/s i) *
        operationalReactionFlux θ (operationalSpecies q s θ w) a := by
  rw [operationalWeightedField, operationalRead_apply,
    restrictedFieldEuclid_threeSite]
  fin_cases i <;>
    simp [operationalStoichiometry, operationalReactionFlux, operationalSpecies,
      operationalParameterRates, threeSiteField, operationalFlatten,
      Fin.sum_univ_succ, div_eq_mul_inv] <;> ring

end
end PhosphorylationStableCapacity

namespace PhosphorylationStableCapacity
noncomputable section
open scoped BigOperators
theorem operationalSpeciesExpression_eval
    (q s : Fin 9 → ℚ) (θ : Fin 21 → ℝ) (w : Fin 9 → ℝ) (i : Fin 12) :
    (operationalSpeciesExpression q s i).eval (operationalInput θ w) =
      operationalSpecies (fun j => (q j : ℝ)) (fun j => (s j : ℝ)) θ w i := by
  simp only [operationalSpeciesExpression, RationalExpression.eval,
    RationalExpression.eval_linearCombination]
  fin_cases i <;>
    simp [operationalCentreExpression, operationalSpeciesLinear, RationalExpression.eval,
      operationalSpecies, operationalUnpack, operationalLift_apply,
      threeSiteFreeS0, threeSiteFreeE, threeSiteFreeF,
      operationalInput, Fin.addCases, Fin.sum_univ_succ]
  all_goals ring

end
end PhosphorylationStableCapacity

namespace PhosphorylationStableCapacity
noncomputable section

theorem operationalFluxExpression_eval
    (e : Fin 12 → RationalExpression (Fin 30)) (θ : Fin 21 → ℝ)
    (w : Fin 9 → ℝ) (a : Fin 18) :
    (operationalFluxExpression e a).eval (operationalInput θ w) =
      operationalReactionFlux θ (fun i => (e i).eval (operationalInput θ w)) a := by
  fin_cases a <;>
    simp [operationalFluxExpression, operationalReactionFirst,
      operationalReactionSecond, RationalExpression.eval,
      operationalInput, Fin.addCases, operationalReactionFlux]

/-- Literal elementary-reaction derivative with respect to one weighted
class coordinate. The matrix T is the exact affine species derivative. -/
def operationalReactionDerivative (θ : Fin 21 → ℝ) (x : Fin 12 → ℝ)
    (T : Matrix (Fin 12) (Fin 9) ℝ) (a : Fin 18) (j : Fin 9) : ℝ :=
  let rate := θ (Fin.castAdd 3 a)
  let first := operationalReactionFirst a
  match operationalReactionSecond a with
  | none => rate*T first j
  | some b => rate*(x first*T b j+x b*T first j)

def operationalNominalReactionDerivative (rates : Fin 18 → ℚ)
    (x : Fin 12 → ℚ) (T : Matrix (Fin 12) (Fin 9) ℚ)
    (a : Fin 18) (j : Fin 9) : ℚ :=
  let first := operationalReactionFirst a
  match operationalReactionSecond a with
  | none => rates a*T first j
  | some b => rates a*(x first*T b j+x b*T first j)

/-- The enclosable expression equals the actual reaction derivative's
perturbation, with the same physical reconstruction at every parameter. -/
theorem operationalDerivativeDifferenceExpression_eval
    (q s : Fin 9 → ℚ) (rates : Fin 18 → ℚ) (nominal : Fin 12 → ℚ)
    (θ : Fin 21 → ℝ) (w : Fin 9 → ℝ) (a : Fin 18) (j : Fin 9) :
    (operationalDerivativeDifferenceExpression q s rates nominal a j).eval
      (operationalInput θ w) =
      operationalReactionDerivative θ
        (operationalSpecies (fun i => (q i : ℝ)) (fun i => (s i : ℝ)) θ w)
        (fun i j => (operationalSpeciesLinear s i j : ℝ)) a j -
      (operationalNominalReactionDerivative rates nominal
        (operationalSpeciesLinear s) a j : ℝ) := by
  fin_cases a <;>
    simp [operationalDerivativeDifferenceExpression,
      operationalReactionFirst, operationalReactionSecond,
      RationalExpression.eval, operationalSpeciesExpression_eval,
      operationalReactionDerivative, operationalNominalReactionDerivative,
      operationalInput, Fin.addCases] <;> ring

end
end PhosphorylationStableCapacity

namespace PhosphorylationStableCapacity
noncomputable section
open scoped BigOperators

theorem operationalCentreExpression_eval
    (q s : Fin 9 → ℚ) (θ : Fin 21 → ℝ) (w : Fin 9 → ℝ) (i : Fin 12) :
    (operationalCentreExpression q i).eval (operationalInput θ w) =
      operationalSpecies (fun j => (q j : ℝ)) (fun j => (s j : ℝ)) θ 0 i := by
  fin_cases i <;>
    simp [operationalCentreExpression, RationalExpression.eval,
      operationalInput, Fin.addCases, operationalSpecies, operationalLift_apply,
      operationalUnpack, threeSiteFreeS0, threeSiteFreeE, threeSiteFreeF,
      Fin.sum_univ_succ] <;> ring

/-- The centre residual expression is the actual field's centre flux,
with only the exact nominal balanced flux subtracted. -/
theorem operationalFluxDifferenceExpression_eval
    (q s : Fin 9 → ℚ) (rates : Fin 18 → ℚ) (nominal : Fin 12 → ℚ)
    (θ : Fin 21 → ℝ) (w : Fin 9 → ℝ) (a : Fin 18) :
    (operationalFluxDifferenceExpression q rates nominal a).eval
      (operationalInput θ w) =
      operationalReactionFlux θ
        (operationalSpecies (fun j => (q j : ℝ)) (fun j => (s j : ℝ)) θ 0) a -
      (operationalNominalFlux rates nominal a : ℝ) := by
  simp only [operationalFluxDifferenceExpression, RationalExpression.eval]
  rw [operationalFluxExpression_eval]
  have hcentre : (fun i => (operationalCentreExpression q i).eval
      (operationalInput θ w)) =
      operationalSpecies (fun j => (q j : ℝ)) (fun j => (s j : ℝ)) θ 0 := by
    funext i
    exact operationalCentreExpression_eval q s θ w i
  rw [hcentre]
  ring

end
end PhosphorylationStableCapacity

namespace PhosphorylationStableCapacity
noncomputable section
open PhosphorylationSharpness Matrix
open scoped BigOperators

/-- The weighted stoichiometry uses the same nine scale factors as the
actual coordinate chart. -/
def operationalWeightedStoichiometry (s : Fin 9 → ℝ) :
    Matrix (Fin 9) (Fin 18) ℝ :=
  fun i a => (operationalStoichiometry i a : ℝ) / s i

/-- Reaction derivatives are entries of the actual class Jacobian, including
the dependence of free substrate and enzymes on the conserved totals. -/
theorem operationalWeightedJacobian_reaction_action
    (q s : Fin 9 → ℚ) (θ : Fin 21 → ℝ) (w v : Fin 9 → ℝ) :
    operationalWeightedJacobian (fun i => (q i : ℝ))
        (fun i => (s i : ℝ)) θ w v =
      (operationalWeightedStoichiometry (fun i => (s i : ℝ)) *
        (Matrix.of fun a j => operationalReactionDerivative θ
          (operationalSpecies (fun i => (q i : ℝ))
            (fun i => (s i : ℝ)) θ w)
          (fun i j => (operationalSpeciesLinear s i j : ℝ)) a j :
          Matrix (Fin 18) (Fin 9) ℝ)) *ᵥ v := by
  ext i
  simp only [operationalWeightedJacobian, ContinuousLinearMap.comp_apply]
  rw [operationalRead_apply, restrictedJacobian_threeSite]
  fin_cases i <;>
    simp [operationalFlatten, operationalLift_apply, operationalUnpack,
      operationalSpecies, operationalParameterRates,
      operationalWeightedStoichiometry, operationalStoichiometry,
      operationalReactionDerivative, operationalReactionFirst,
      operationalReactionSecond, operationalSpeciesLinear,
      threeSiteJacobianCLM, threeSiteRowS1, threeSiteRowS2, threeSiteRowS3,
      threeSiteRowC0, threeSiteRowC1, threeSiteRowC2,
      threeSiteRowD0, threeSiteRowD1, threeSiteRowD2,
      threeSiteS0Linear, threeSiteELinear, threeSiteFLinear,
      threeSitePS, threeSitePC, threeSitePD,
      threeSiteFreeS0, threeSiteFreeE, threeSiteFreeF,
      Matrix.mul_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_succ,
      div_eq_mul_inv] <;> ring

end
end PhosphorylationStableCapacity

namespace PhosphorylationStableCapacity
noncomputable section
open PhosphorylationSharpness

/-- The operational field has the exact quadratic midpoint identity in the
same weighted coordinates used by the interval and Lyapunov certificates. -/
theorem operationalWeightedField_midpoint
    (q s : Fin 9 → ℝ) (θ : Fin 21 → ℝ) (x v : Fin 9 → ℝ) :
    operationalWeightedField q s θ (x+v) -
      operationalWeightedField q s θ x =
        operationalWeightedJacobian q s θ (x+(1/2 : ℝ) • v) v := by
  have hsum : operationalUnpack q+operationalLift s (x+v) =
      (operationalUnpack q+operationalLift s x)+operationalLift s v := by
    rw [map_add]
    abel
  have hmid : (operationalUnpack q+operationalLift s x)+
      (1/2 : ℝ) • operationalLift s v =
      operationalUnpack q+operationalLift s (x+(1/2 : ℝ) • v) := by
    rw [map_add, map_smul]
    abel
  unfold operationalWeightedField operationalWeightedJacobian
  rw [← map_sub, hsum, restrictedFieldEuclid_midpoint_threeSite, hmid]
  rfl

end
end PhosphorylationStableCapacity

namespace PhosphorylationStableCapacity
noncomputable section
open PhosphorylationSharpness Set

/-- A forward solution of the literal mass-action field in the operational
weighted coordinates. Its existence is part of the physical correspondence. -/
def IsOperationalForwardCurve (q s : Fin 9 → ℝ) (θ : Fin 21 → ℝ)
    (initial : Fin 9 → ℝ) (γ : ℝ → Fin 9 → ℝ) : Prop :=
  γ 0 = initial ∧ ∀ t : ℝ, 0 ≤ t →
    HasDerivWithinAt γ (operationalWeightedField q s θ (γ t)) (Ici (0 : ℝ)) t

theorem exists_operational_forward_curve
    (q s : Fin 9 → ℝ) (hs : ∀ i, s i ≠ 0) (θ : Fin 21 → ℝ)
    (hET : 0 < θ 18) (hk : (operationalParameterRates θ).Positive)
    (initial : Fin 9 → ℝ)
    (hinitial : operationalUnpack q+operationalLift s initial ∈
      classPolytope 3 (θ 18) (θ 19) (θ 20)) :
    ∃ γ : ℝ → Fin 9 → ℝ, IsOperationalForwardCurve q s θ initial γ := by
  obtain ⟨β, hβ, _hphysical⟩ := exists_physical_forward_class_curve
    (θ 18) (θ 19) (θ 20) hET (operationalParameterRates θ) hk
    (operationalUnpack q+operationalLift s initial) hinitial
  let γ : ℝ → Fin 9 → ℝ := fun t => operationalRead s (β t-operationalUnpack q)
  have hembed (t : ℝ) : operationalUnpack q+operationalLift s (γ t) = β t := by
    dsimp only [γ]
    rw [operationalLift_read s hs]
    abel
  refine ⟨γ, ?_, ?_⟩
  · dsimp only [γ]
    rw [hβ.1, add_sub_cancel_left, operationalRead_lift s hs]
  · intro t ht
    have hder := (operationalRead s).hasFDerivAt.comp_hasDerivWithinAt t
      ((hβ.2 t ht).sub_const (operationalUnpack q))
    have hfield : operationalRead s
        (restrictedFieldEuclid (θ 18) (θ 19) (θ 20)
          (operationalParameterRates θ) (β t)) =
        operationalWeightedField q s θ (γ t) := by
      unfold operationalWeightedField
      rw [hembed]
    rw [hfield] at hder
    exact hder

theorem operationalForwardCurve_coordinate_derivative
    (q s : Fin 9 → ℝ) (θ : Fin 21 → ℝ) (initial : Fin 9 → ℝ)
    (γ : ℝ → Fin 9 → ℝ) (hγ : IsOperationalForwardCurve q s θ initial γ)
    (t : ℝ) (ht : 0 ≤ t) (i : Fin 9) :
    HasDerivWithinAt (fun u => γ u i)
      (operationalWeightedField q s θ (γ t) i) (Ici (0 : ℝ)) t := by
  exact (operationalProjection i).hasFDerivAt.comp_hasDerivWithinAt t (hγ.2 t ht)

end
end PhosphorylationStableCapacity

namespace PhosphorylationStableCapacity
noncomputable section
open PhosphorylationSharpness
open scoped BigOperators

theorem operationalSpecies_eq_reconstructed
    (q s : Fin 9 → ℝ) (θ : Fin 21 → ℝ) (w : Fin 9 → ℝ) :
    operationalSpecies q s θ w =
      let x := unChart (θ 18) (θ 19) (θ 20)
        (ofCoordinateSpace (operationalUnpack q+operationalLift s w))
      ![x.S 0,x.S 1,x.S 2,x.S 3,x.E,x.F,
        x.C 0,x.C 1,x.C 2,x.D 0,x.D 1,x.D 2] := by
  ext i
  fin_cases i
  all_goals norm_num [operationalSpecies, unChart, ofCoordinateSpace,
    operationalUnpack, operationalLift_apply, threeSiteFreeS0,
    threeSiteFreeE, threeSiteFreeF,
    Fin.sum_univ_succ]
  all_goals first | rfl | ring

theorem operationalSpecies_positive_state
    (q s : Fin 9 → ℝ) (θ : Fin 21 → ℝ) (w : Fin 9 → ℝ)
    (h : ∀ i : Fin 12, 0 < operationalSpecies q s θ w i) :
    (unChart (θ 18) (θ 19) (θ 20)
      (ofCoordinateSpace (operationalUnpack q+operationalLift s w))).Positive := by
  let x := unChart (θ 18) (θ 19) (θ 20)
    (ofCoordinateSpace (operationalUnpack q+operationalLift s w))
  have hs (i : Fin 12) : 0 <
      ![x.S 0,x.S 1,x.S 2,x.S 3,x.E,x.F,
        x.C 0,x.C 1,x.C 2,x.D 0,x.D 1,x.D 2] i := by
    simpa only [operationalSpecies_eq_reconstructed] using h i
  refine ⟨?_, hs 4, hs 5, ?_, ?_⟩
  · intro i
    fin_cases i
    · exact hs 0
    · exact hs 1
    · exact hs 2
    · exact hs 3
  · intro i
    fin_cases i
    · exact hs 6
    · exact hs 7
    · exact hs 8
  · intro i
    fin_cases i
    · exact hs 9
    · exact hs 10
    · exact hs 11

theorem operationalParameterRates_positive
    (θ : Fin 21 → ℝ) (h : ∀ i, 0 < θ i) :
    (operationalParameterRates θ).Positive := by
  intro i
  fin_cases i
  · exact ⟨h 0,h 1,h 2,h 3,h 4,h 5⟩
  · exact ⟨h 6,h 7,h 8,h 9,h 10,h 11⟩
  · exact ⟨h 12,h 13,h 14,h 15,h 16,h 17⟩

end
end PhosphorylationStableCapacity
