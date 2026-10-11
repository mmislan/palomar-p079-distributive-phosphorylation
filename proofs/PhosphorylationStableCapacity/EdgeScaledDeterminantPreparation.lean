module
public import proofs.PhosphorylationStableCapacity.SplitRelaxDeterminant
public import proofs.PhosphorylationStableCapacity.EdgeScaledLoadedField
public import proofs.PhosphorylationStableCapacity.ProjectedPathIncidence

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section

open PhosphorylationSharpness Matrix

def catalyticCurrent {n : ℕ} (k : Rates n) (x : State n)
    (i : Fin n) : ℝ := k.c i * x.C i - k.gamma i * x.D i

/-- The literal loaded slow field is the projected path incidence of the
current vector, at every state in every compatibility class. -/
theorem loadedRestrictedField_slow_eq_incidence {n : ℕ}
    (ET FT ST : ℝ) (k : Rates n) (u : CoordinateSpace n) :
    (loadedRestrictedField ET FT ST k u).1 =
      (projectedPathIncidence n).mulVec
        (catalyticCurrent k (stateFromLoaded ET FT ST u)) := by
  funext i
  rw [loadedRestrictedField_slow]
  rw [projectedPathIncidence_mulVec]
  rw [loadedLevel_field_eq_catalytic_flux]
  simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply,
    catalyticCurrent]
  apply Finset.sum_congr rfl
  intro j _
  have hsucc : (j.succ = i.succ) ↔ (i = j) := by
    constructor
    · intro h
      exact (Fin.succ_injective n h).symm
    · intro h
      rw [h]
  have hself : j.castSucc ≠ j.succ := by
    intro h
    have hv := congrArg Fin.val h
    simp only [Fin.val_castSucc, Fin.val_succ] at hv
    omega
  by_cases h1 : i = j
  <;> by_cases h2 : j.castSucc = i.succ
  <;> simp [pathIncidence, stateFromLoaded, hsucc, hself, h1, h2, eq_comm]

theorem edgeScaledRates_loaded_slow_eq_incidence {n : ℕ}
    (ET FT ST : ℝ) (w : Fin n → ℝ) (k : Rates n)
    (u : CoordinateSpace n) :
    (loadedRestrictedField ET FT ST (edgeScaledRates w k) u).1 =
      (projectedPathIncidence n).mulVec
        (fun i => w i * catalyticCurrent k (stateFromLoaded ET FT ST u) i) := by
  rw [loadedRestrictedField_slow_eq_incidence]
  congr 1
  funext i
  simp [catalyticCurrent, edgeScaledRates]
  ring

/-- The edge-current scaling transported into loaded slow coordinates. -/
def edgeScaleSlowMatrix (n : ℕ) (w : Fin n → ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  projectedPathIncidence n * Matrix.diagonal w *
    (projectedPathIncidence n)⁻¹

theorem edgeScaleSlowMatrix_det (n : ℕ) (w : Fin n → ℝ) :
    (edgeScaleSlowMatrix n w).det = ∏ i, w i := by
  simp [edgeScaleSlowMatrix, Matrix.det_mul, Matrix.det_diagonal,
    Matrix.det_nonsing_inv, projectedPathIncidence_det]

theorem edgeScaleSlowMatrix_det_pos (n : ℕ) (w : Fin n → ℝ)
    (hw : ∀ i, 0 < w i) :
    0 < (edgeScaleSlowMatrix n w).det := by
  rw [edgeScaleSlowMatrix_det]
  exact Finset.prod_pos (fun i _ => hw i)

theorem edgeScaledRates_loaded_slow_linear (n : ℕ)
    (ET FT ST : ℝ) (w : Fin n → ℝ) (k : Rates n)
    (u : CoordinateSpace n) :
    (loadedRestrictedField ET FT ST (edgeScaledRates w k) u).1 =
      (edgeScaleSlowMatrix n w).mulVec
        (loadedRestrictedField ET FT ST k u).1 := by
  let T := projectedPathIncidence n
  let c := catalyticCurrent k (stateFromLoaded ET FT ST u)
  have hbase := loadedRestrictedField_slow_eq_incidence ET FT ST k u
  have hscaled := edgeScaledRates_loaded_slow_eq_incidence ET FT ST w k u
  change (loadedRestrictedField ET FT ST (edgeScaledRates w k) u).1 =
    (T * Matrix.diagonal w * T⁻¹).mulVec
      (loadedRestrictedField ET FT ST k u).1
  rw [hbase, hscaled]
  have hdet : IsUnit T.det := by
    change IsUnit (projectedPathIncidence n).det
    rw [projectedPathIncidence_det]
    exact isUnit_one
  calc
    T.mulVec (fun i => w i * c i) =
        T.mulVec ((Matrix.diagonal w).mulVec c) := by
          congr 1
          funext i
          simp [Matrix.mulVec_diagonal]
    _ = (T * Matrix.diagonal w).mulVec c := by
          rw [Matrix.mulVec_mulVec]
    _ = (T * Matrix.diagonal w * T⁻¹).mulVec (T.mulVec c) := by
          simp only [Matrix.mulVec_mulVec, Matrix.mul_assoc,
            Matrix.nonsing_inv_mul T hdet, Matrix.mul_one]

def edgeScaleLoadedOutput (n : ℕ) (w : Fin n → ℝ)
    (v : CoordinateSpace n) : CoordinateSpace n :=
  ((edgeScaleSlowMatrix n w).mulVec v.1,
    fun i => w i * v.2.1 i,
    fun i => w i * v.2.2 i)

/-- Edge-rate scaling acts on the full loaded class field by one fixed
linear output transformation, uniformly at every state. -/
theorem edgeScaledRates_loadedField_eq_output {n : ℕ}
    (ET FT ST : ℝ) (w : Fin n → ℝ) (k : Rates n)
    (u : CoordinateSpace n) :
    loadedRestrictedField ET FT ST (edgeScaledRates w k) u =
      edgeScaleLoadedOutput n w (loadedRestrictedField ET FT ST k u) := by
  apply Prod.ext
  · exact edgeScaledRates_loaded_slow_linear n ET FT ST w k u
  · apply Prod.ext <;> funext i
    · exact edgeScaledRates_loadedRestrictedField_C ET FT ST w k u i
    · exact edgeScaledRates_loadedRestrictedField_D ET FT ST w k u i

def edgeScaleLoadedOutputLinear (n : ℕ) (w : Fin n → ℝ) :
    CoordinateSpace n →ₗ[ℝ] CoordinateSpace n where
  toFun := edgeScaleLoadedOutput n w
  map_add' a b := by
    apply Prod.ext
    · simp [edgeScaleLoadedOutput, Matrix.mulVec_add]
    · apply Prod.ext <;> funext i <;>
        simp [edgeScaleLoadedOutput, mul_add]
  map_smul' c a := by
    apply Prod.ext
    · simp [edgeScaleLoadedOutput, Matrix.mulVec_smul]
    · apply Prod.ext <;> funext i <;>
        simp [edgeScaleLoadedOutput, smul_eq_mul] <;> ring

theorem edgeScaleLoadedOutputLinear_toMatrix (n : ℕ)
    (w : Fin n → ℝ) :
    LinearMap.toMatrix (coordinateBasis n) (coordinateBasis n)
      (edgeScaleLoadedOutputLinear n w) =
    Matrix.fromBlocks (edgeScaleSlowMatrix n w) 0 0
      (Matrix.fromBlocks (Matrix.diagonal w) 0 0 (Matrix.diagonal w)) := by
  ext i j
  rcases i with i | i | i <;> rcases j with j | j | j <;>
    simp [edgeScaleLoadedOutputLinear, edgeScaleLoadedOutput,
      coordinateBasis, Matrix.fromBlocks_apply₁₁,
      Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁,
      Matrix.fromBlocks_apply₂₂, LinearMap.toMatrix_apply,
      Module.Basis.prod_repr_inl, Module.Basis.prod_repr_inr]
  <;> simp [Matrix.diagonal, Pi.single_apply]

theorem edgeScaleLoadedOutputLinear_det (n : ℕ)
    (w : Fin n → ℝ) :
    (LinearMap.toMatrix (coordinateBasis n) (coordinateBasis n)
      (edgeScaleLoadedOutputLinear n w)).det =
        (∏ i, w i) ^ 3 := by
  rw [edgeScaleLoadedOutputLinear_toMatrix,
    Matrix.det_fromBlocks_zero₂₁, Matrix.det_fromBlocks_zero₂₁,
    edgeScaleSlowMatrix_det, Matrix.det_diagonal]
  ring

def edgeScaleLoadedOutputCLM (n : ℕ) (w : Fin n → ℝ) :
    CoordinateSpace n →L[ℝ] CoordinateSpace n :=
  (edgeScaleLoadedOutputLinear n w).toContinuousLinearMap

theorem edgeScaledRates_loadedFderiv_eq_comp {n : ℕ}
    (ET FT ST : ℝ) (w : Fin n → ℝ) (k : Rates n)
    (u : CoordinateSpace n) :
    fderiv ℝ (loadedRestrictedField ET FT ST (edgeScaledRates w k)) u =
      (edgeScaleLoadedOutputCLM n w).comp
        (fderiv ℝ (loadedRestrictedField ET FT ST k) u) := by
  have hfun : loadedRestrictedField ET FT ST (edgeScaledRates w k) =
      (edgeScaleLoadedOutputCLM n w) ∘
        loadedRestrictedField ET FT ST k := by
    funext v
    exact edgeScaledRates_loadedField_eq_output ET FT ST w k v
  have hdiff : DifferentiableAt ℝ (loadedRestrictedField ET FT ST k) u := by
    rw [loadedRestrictedField_conjugate]
    exact (loadedCoordContinuous n).differentiableAt.comp u
      ((differentiable_restrictedFieldEuclid ET FT ST k).differentiableAt.comp u
        (loadedCoordContinuous n).symm.differentiableAt)
  rw [hfun]
  change fderiv ℝ
    ((edgeScaleLoadedOutputCLM n w) ∘ loadedRestrictedField ET FT ST k) u = _
  rw [fderiv_comp u (edgeScaleLoadedOutputCLM n w).differentiableAt hdiff]
  rw [ContinuousLinearMap.fderiv]

theorem loadedJacobianMatrix_edgeScaled_det {n : ℕ}
    (ET FT ST : ℝ) (w : Fin n → ℝ) (k : Rates n)
    (u : CoordinateSpace n) :
    (loadedJacobianMatrix ET FT ST (edgeScaledRates w k) u).det =
      (∏ i, w i) ^ 3 * (loadedJacobianMatrix ET FT ST k u).det := by
  unfold loadedJacobianMatrix
  rw [edgeScaledRates_loadedFderiv_eq_comp]
  change (LinearMap.toMatrix (coordinateBasis n) (coordinateBasis n)
    ((edgeScaleLoadedOutputLinear n w).comp
      (fderiv ℝ (loadedRestrictedField ET FT ST k) u).toLinearMap)).det = _
  rw [LinearMap.toMatrix_comp (coordinateBasis n) (coordinateBasis n)
    (coordinateBasis n) (edgeScaleLoadedOutputLinear n w)
    (fderiv ℝ (loadedRestrictedField ET FT ST k) u).toLinearMap,
    Matrix.det_mul,
    edgeScaleLoadedOutputLinear_det]

theorem restrictedJacobianMatrix_edgeScaled_det {n : ℕ}
    (ET FT ST : ℝ) (w : Fin n → ℝ) (k : Rates n)
    (u : CoordinateSpace n) :
    (restrictedJacobianMatrix ET FT ST (edgeScaledRates w k)
      (fromLoadedCoord u)).det =
      (∏ i, w i) ^ 3 *
        (restrictedJacobianMatrix ET FT ST k
          (fromLoadedCoord u)).det := by
  rw [restrictedJacobianMatrix_det_eq_loaded,
    restrictedJacobianMatrix_det_eq_loaded,
    loadedJacobianMatrix_edgeScaled_det]

theorem restrictedJacobianMatrix_edgeScaled_det_sign {n : ℕ}
    (ET FT ST : ℝ) (w : Fin n → ℝ) (k : Rates n)
    (u : CoordinateSpace n) (hw : ∀ i, 0 < w i) :
    ((restrictedJacobianMatrix ET FT ST (edgeScaledRates w k)
        (fromLoadedCoord u)).det < 0 ↔
      (restrictedJacobianMatrix ET FT ST k (fromLoadedCoord u)).det < 0) ∧
    (0 < (restrictedJacobianMatrix ET FT ST (edgeScaledRates w k)
        (fromLoadedCoord u)).det ↔
      0 < (restrictedJacobianMatrix ET FT ST k (fromLoadedCoord u)).det) := by
  rw [restrictedJacobianMatrix_edgeScaled_det]
  have hfac : 0 < (∏ i, w i) ^ 3 :=
    pow_pos (Finset.prod_pos (fun i _ => hw i)) _
  constructor
  · simpa using (mul_lt_mul_iff_of_pos_left hfac (b :=
      (restrictedJacobianMatrix ET FT ST k (fromLoadedCoord u)).det)
      (c := 0))
  · exact mul_pos_iff_of_pos_left hfac

end
end PhosphorylationStableCapacity
