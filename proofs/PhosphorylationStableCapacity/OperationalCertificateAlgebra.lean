module
public import proofs.PhosphorylationStableCapacity.MatrixAbsoluteRowOperatorBound
public import proofs.PhosphorylationStableCapacity.ScaledIntegerMatrixCertificates
public import proofs.PhosphorylationStableCapacity.OperationalReactionExpressions
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Rat.Cast.Lemmas
public import Mathlib.Data.Rat.Cast.CharZero
public import Mathlib.Analysis.Normed.Group.Real
public import Mathlib.Analysis.Normed.Group.Constructions
public import Mathlib.Tactic.NoncommRing
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum

@[expose] public section

set_option maxHeartbeats 2000000

namespace PhosphorylationStableCapacity
noncomputable section
open Matrix

/-- Precontracting the fixed inverse with stoichiometry retains the exact
Newton residual; it does not change the field being certified. -/
theorem precontracted_newton_residual
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (R : Matrix ι ι ℝ) (B C : Matrix ι κ ℝ)
    (hC : C = R*B) (flux : κ → ℝ) :
    R *ᵥ (B *ᵥ flux) = C *ᵥ flux := by
  rw [hC, Matrix.mulVec_mulVec]

/-- The derivative certificate bounds the actual Newton derivative, after
subtracting the exact nominal Jacobian and using its checked inverse. -/
theorem precontracted_newton_defect
    {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι]
    (R J J₀ : Matrix ι ι ℝ) (B C : Matrix ι κ ℝ)
    (D : Matrix κ ι ℝ) (hC : C = R*B)
    (hR : R*J₀ = 1) (hD : J = J₀+B*D) :
    1-R*J = -(C*D) := by
  rw [hD, Matrix.mul_add, hR, ← Matrix.mul_assoc, ← hC]
  abel

/-- The precontracted symmetric loss is precisely the perturbation of the
fixed common Lyapunov form, for the actual perturbed Jacobian. -/
theorem precontracted_lyapunov_loss
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (P J J₀ Q : Matrix ι ι ℝ) (B C : Matrix ι κ ℝ)
    (D : Matrix κ ι ℝ) (hP : P.IsSymm)
    (hC : C = P*B) (hD : J = J₀+B*D)
    (hQ : J₀.transpose*P+P*J₀ = -Q) :
    J.transpose*P+P*J = -Q+(C*D+(C*D).transpose) := by
  have hPt : P.transpose = P := hP
  rw [hC, Matrix.mul_assoc]
  rw [Matrix.transpose_mul, hPt]
  rw [hD, Matrix.transpose_add, Matrix.add_mul, Matrix.mul_add]
  rw [← hQ]
  abel

end
end PhosphorylationStableCapacity


namespace PhosphorylationStableCapacity.ScaledIntegerMatrix
noncomputable section

/-- Exact rational decoding for small finite semantic correspondence checks. -/
def rationalMatrix {ι κ : Type*} (A : ScaledIntegerMatrix ι κ) : Matrix ι κ ℚ :=
  (A.denominator : ℚ)⁻¹ • A.entries.map (Int.castRingHom ℚ)

theorem realMatrix_eq_rational_cast {ι κ : Type*}
    (A : ScaledIntegerMatrix ι κ) :
    A.realMatrix = A.rationalMatrix.map (Rat.castHom ℝ) := by
  ext i j
  simp only [realMatrix, rationalMatrix, Matrix.map_apply, Matrix.smul_apply,
    smul_eq_mul]
  change (A.denominator : ℝ)⁻¹ * (A.entries i j : ℝ) =
    (((A.denominator : ℚ)⁻¹ * (A.entries i j : ℚ) : ℚ) : ℝ)
  simp only [Rat.cast_mul, Rat.cast_inv, Rat.cast_natCast, Rat.cast_intCast]

theorem realMatrix_isSymm_of_integer {ι : Type*}
    (A : ScaledIntegerMatrix ι ι) (hA : A.entries.IsSymm) :
    A.realMatrix.IsSymm := by
  ext i j
  change (A.denominator : ℝ)⁻¹ * (A.entries j i : ℝ) =
    (A.denominator : ℝ)⁻¹ * (A.entries i j : ℝ)
  rw [hA.apply i j]

end
end PhosphorylationStableCapacity.ScaledIntegerMatrix


namespace PhosphorylationStableCapacity
noncomputable section
open Matrix
open scoped BigOperators

/-- A matrix acting on the ordinary finite product with its sup norm. -/
def matrixSupContinuousMap {ι κ : Type*} [Fintype ι] [Fintype κ]
    (M : Matrix ι κ ℝ) : (κ → ℝ) →L[ℝ] (ι → ℝ) :=
  ContinuousLinearMap.pi (fun i => ∑ j, M i j •
    (ContinuousLinearMap.proj j : (κ → ℝ) →L[ℝ] ℝ))

theorem matrixSupContinuousMap_apply {ι κ : Type*} [Fintype ι] [Fintype κ]
    (M : Matrix ι κ ℝ) (v : κ → ℝ) :
    matrixSupContinuousMap M v = M *ᵥ v := by
  ext i
  simp [matrixSupContinuousMap, Matrix.mulVec, dotProduct]

theorem matrixSupContinuousMap_injective_of_left_inverse
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M N : Matrix ι ι ℝ) (hMN : M*N = 1) :
    Function.Injective (matrixSupContinuousMap N) := by
  intro u v h
  have hmul := congrArg (fun w => M *ᵥ w) h
  simp only [matrixSupContinuousMap_apply, Matrix.mulVec_mulVec,
    hMN, Matrix.one_mulVec] at hmul
  exact hmul

theorem matrixSupContinuousMap_newton_defect_norm
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (R J : Matrix ι ι ℝ) (A : (ι → ℝ) →L[ℝ] (ι → ℝ))
    (hA : ∀ v, A v = J *ᵥ v) (B : ℝ) (hB : 0 ≤ B)
    (hrows : ∀ i, (∑ j, |(1-R*J) i j|) ≤ B) :
    ‖ContinuousLinearMap.id ℝ (ι → ℝ) -
      (matrixSupContinuousMap R).comp A‖ ≤ B := by
  apply continuousLinearMap_norm_le_of_absolute_rows _ (1-R*J) _ B hB hrows
  intro v
  simp only [_root_.sub_apply, ContinuousLinearMap.id_apply,
    ContinuousLinearMap.comp_apply, matrixSupContinuousMap_apply, hA,
    Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.mulVec_mulVec]

/-- Absolute row sums also give the exact induced infinity norm when the
finite maximum is attained; the maximizing vector uses only signs. -/
theorem matrixSupContinuousMap_absolute_row_le_norm
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (M : Matrix ι κ ℝ) (i : ι) :
    (∑ j, |M i j|) ≤ ‖matrixSupContinuousMap M‖ := by
  classical
  let v : κ → ℝ := fun j => if 0 ≤ M i j then 1 else -1
  have hv : ‖v‖ ≤ 1 := by
    apply (pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 1)).mpr
    intro j
    dsimp only [v]
    split_ifs <;> norm_num
  have heval : matrixSupContinuousMap M v i = ∑ j, |M i j| := by
    rw [matrixSupContinuousMap_apply]
    change (∑ j, M i j*v j) = ∑ j, |M i j|
    apply Finset.sum_congr rfl
    intro j _hj
    by_cases hj : 0 ≤ M i j
    · simp [v, hj, abs_of_nonneg hj]
    · simp [v, hj, abs_of_neg (lt_of_not_ge hj)]
  have hnonneg : 0 ≤ ∑ j, |M i j| :=
    Finset.sum_nonneg (fun _j _hj => abs_nonneg _)
  have hcoord := norm_le_pi_norm (matrixSupContinuousMap M v) i
  rw [Real.norm_eq_abs, heval, abs_of_nonneg hnonneg] at hcoord
  calc
    _ ≤ ‖matrixSupContinuousMap M v‖ := hcoord
    _ ≤ ‖matrixSupContinuousMap M‖ * ‖v‖ := (matrixSupContinuousMap M).le_opNorm v
    _ ≤ ‖matrixSupContinuousMap M‖ := by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hv (norm_nonneg _)

theorem matrixSupContinuousMap_norm_eq_row_max
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (M : Matrix ι κ ℝ) (B : ℝ) (hB : 0 ≤ B)
    (hrows : ∀ i, (∑ j, |M i j|) ≤ B)
    (hpeak : ∃ i, (∑ j, |M i j|) = B) :
    ‖matrixSupContinuousMap M‖ = B := by
  apply le_antisymm
  · exact continuousLinearMap_norm_le_of_absolute_rows _ M
      (matrixSupContinuousMap_apply M) B hB hrows
  · obtain ⟨i, hi⟩ := hpeak
    rw [← hi]
    exact matrixSupContinuousMap_absolute_row_le_norm M i

end
end PhosphorylationStableCapacity


namespace PhosphorylationStableCapacity
noncomputable section

def operationalIndependentDomain (nominal : Fin 21 → ℚ) (η ρ : ℚ) :
    Fin 30 → RationalInterval :=
  fun i => Fin.addCases (m := 21) (n := 9) (fun j => RationalInterval.relative (nominal j) η)
    (fun _ => RationalInterval.centered 0 ρ) i

/-- The closed coordinate ball and all21 independent relative parameter
perturbations lie in the same input box used by the interval checker. -/
theorem operationalInput_mem_independent_domain
    (nominal : Fin 21 → ℚ) (η ρ : ℚ) (θ : Fin 21 → ℝ) (w : Fin 9 → ℝ)
    (hθ : ∀ i, |θ i-(nominal i : ℝ)| ≤ (η : ℝ)*(nominal i : ℝ))
    (hw : ‖w‖ ≤ (ρ : ℝ)) :
    ∀ i, (operationalIndependentDomain nominal η ρ i).Contains
      (operationalInput θ w i) := by
  intro i
  refine Fin.addCases (m := 21) (n := 9) (fun j => ?_) (fun j => ?_) i
  · simpa only [operationalIndependentDomain, operationalInput, Fin.addCases_left]
      using RationalInterval.relative_contains_of_abs_sub_le (nominal j) η (θ j) (hθ j)
  · have hj : |w j-(0 : ℚ)| ≤ (ρ : ℝ) := by
      simpa only [Rat.cast_zero, sub_zero, Real.norm_eq_abs] using
        (norm_le_pi_norm w j).trans hw
    simpa only [operationalIndependentDomain, operationalInput, Fin.addCases_right]
      using RationalInterval.centered_contains_of_abs_sub_le 0 ρ (w j) hj

theorem operational_independent_parameters_positive
    (nominal : Fin 21 → ℚ) (η : ℚ) (θ : Fin 21 → ℝ)
    (hnominal : ∀ i, 0 < nominal i) (hη : η < 1)
    (hθ : ∀ i, |θ i-(nominal i : ℝ)| ≤ (η : ℝ)*(nominal i : ℝ)) :
    ∀ i, 0 < θ i := by
  intro i
  have hpos : (0 : ℝ) < nominal i := Rat.cast_pos.mpr (hnominal i)
  have hηreal : (η : ℝ) < 1 := by exact_mod_cast hη
  have hlo := (abs_le.mp (hθ i)).1
  nlinarith

end
end PhosphorylationStableCapacity


namespace PhosphorylationStableCapacity

def operationalRationalCentreSpecies (q : Fin 9 → ℚ) (nominal : Fin 21 → ℚ) :
    Fin 12 → ℚ :=
  ![nominal 20-q 0-q 1-q 2-q 3-q 4-q 5-q 6-q 7-q 8,
    q 0,q 1,q 2,nominal 18-q 3-q 4-q 5,nominal 19-q 6-q 7-q 8,
    q 3,q 4,q 5,q 6,q 7,q 8]

def operationalRationalStoichiometry (s : Fin 9 → ℚ) :
    Matrix (Fin 9) (Fin 18) ℚ := Matrix.of
  ![![0,0,1/s 0,-1/s 0,1/s 0,0,-1/s 0,1/s 0,0,0,0,1/s 0,0,0,0,0,0,0],
    ![0,0,0,0,0,0,0,0,1/s 1,-1/s 1,1/s 1,0,-1/s 1,1/s 1,0,0,0,1/s 1],
    ![0,0,0,0,0,0,0,0,0,0,0,0,0,0,1/s 2,-1/s 2,1/s 2,0],
    ![1/s 3,-1/s 3,-1/s 3,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
    ![0,0,0,0,0,0,1/s 4,-1/s 4,-1/s 4,0,0,0,0,0,0,0,0,0],
    ![0,0,0,0,0,0,0,0,0,0,0,0,1/s 5,-1/s 5,-1/s 5,0,0,0],
    ![0,0,0,1/s 6,-1/s 6,-1/s 6,0,0,0,0,0,0,0,0,0,0,0,0],
    ![0,0,0,0,0,0,0,0,0,1/s 7,-1/s 7,-1/s 7,0,0,0,0,0,0],
    ![0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1/s 8,-1/s 8,-1/s 8]]

def operationalRationalDerivative (s : Fin 9 → ℚ) (rates : Fin 18 → ℚ)
    (x : Fin 12 → ℚ) : Matrix (Fin 18) (Fin 9) ℚ :=
  fun a j =>
    let first := operationalReactionFirst a
    match operationalReactionSecond a with
    | none => rates a*operationalSpeciesLinear s first j
    | some b => rates a*(x first*operationalSpeciesLinear s b j+
        x b*operationalSpeciesLinear s first j)

end PhosphorylationStableCapacity
