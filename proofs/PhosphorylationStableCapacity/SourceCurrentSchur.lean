module
public import proofs.PhosphorylationStableCapacity.LoadedProjectionSlowField
public import proofs.PhosphorylationStableCapacity.ProjectedPathIncidence
public import proofs.PhosphorylationStableCapacity.FastBindingEnergy
public import proofs.PhosphorylationStableCapacity.LoadedJacobianFourBlocks
public import proofs.PhosphorylationStableCapacity.SourceSchurDeterminant

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section
open PhosphorylationSharpness

/-- Catalytic currents depend on the two complex lists alone in loaded coordinates. -/
def loadedCatalyticCurrent {n : ℕ} (k : Rates n)
    (f : FastSpace n) (i : Fin n) : ℝ :=
  k.c i * f.1 i - k.gamma i * f.2 i

/-- The literal slow class field is the projected incidence of catalytic currents. -/
theorem loadedRestrictedField_slow_eq_incidence_current {n : ℕ}
    (ET FT ST : ℝ) (k : Rates n) (u : CoordinateSpace n) :
    (loadedRestrictedField ET FT ST k u).1 =
      (projectedPathIncidence n).mulVec
        (loadedCatalyticCurrent k u.2) := by
  funext i
  rw [loadedRestrictedField_slow, loadedLevel_field_eq_catalytic_flux]
  simp only [projectedPathIncidence_mulVec]
  simp [Matrix.mulVec, dotProduct, pathIncidence,
    loadedCatalyticCurrent, unChart, ofCoordinateSpace,
    fromLoadedCoord, Finset.sum_sub_distrib, sub_mul]
  apply Finset.sum_congr rfl
  intro x _
  by_cases h : x.castSucc = i.succ <;> simp [h, eq_comm]

/-- The edge catalytic-current map is linear in the complex concentrations. -/
def loadedCatalyticCurrentLinear {n : ℕ} (k : Rates n) :
    FastSpace n →ₗ[ℝ] SlowSpace n where
  toFun := loadedCatalyticCurrent k
  map_add' f g := by
    funext i
    simp [loadedCatalyticCurrent, mul_add]
    ring
  map_smul' c f := by
    funext i
    simp [loadedCatalyticCurrent, smul_eq_mul]
    ring

/-- The slow field, viewed as a linear map of the fast coordinates. -/
def loadedSlowCurrentLinear {n : ℕ} (k : Rates n) :
    FastSpace n →ₗ[ℝ] SlowSpace n :=
  (Matrix.mulVecBilin ℝ ℝ (projectedPathIncidence n)).comp
    (loadedCatalyticCurrentLinear k)

/-- The current-to-slow matrix has the path incidence as its left factor. -/
theorem loadedSlowCurrentLinear_toMatrix {n : ℕ} (k : Rates n) :
    LinearMap.toMatrix (fastBasis n) (Pi.basisFun ℝ (Fin n))
      (loadedSlowCurrentLinear k) =
      projectedPathIncidence n *
        LinearMap.toMatrix (fastBasis n) (Pi.basisFun ℝ (Fin n))
          (loadedCatalyticCurrentLinear k) := by
  rw [loadedSlowCurrentLinear,
    LinearMap.toMatrix_comp (fastBasis n) (Pi.basisFun ℝ (Fin n))
      (Pi.basisFun ℝ (Fin n))]
  congr 1
  exact LinearMap.toMatrix'_toLin' (projectedPathIncidence n)

/-- Its extension to all loaded class coordinates ignores the slow input. -/
def loadedSlowCurrentFullLinear {n : ℕ} (k : Rates n) :
    CoordinateSpace n →ₗ[ℝ] SlowSpace n where
  toFun u := loadedSlowCurrentLinear k u.2
  map_add' u v := by
    exact map_add (loadedSlowCurrentLinear k) u.2 v.2
  map_smul' c u := by
    exact map_smul (loadedSlowCurrentLinear k) c u.2

theorem loadedBlockA_eq_zero {n : ℕ} (ET FT ST : ℝ)
    (k : Rates n) (u : CoordinateSpace n) :
    loadedBlockA ET FT ST k u = 0 := by
  have hf := (differentiable_loadedRestrictedField ET FT ST k).differentiableAt
    (x := u)
  have hfun : (fun v : CoordinateSpace n =>
      (loadedRestrictedField ET FT ST k v).1) =
      loadedSlowCurrentFullLinear k := by
    funext v
    exact loadedRestrictedField_slow_eq_incidence_current ET FT ST k v
  have hd := (loadedSlowCurrentFullLinear k).toContinuousLinearMap.hasFDerivAt
    (x := u)
  have hderiv : fderiv ℝ (fun v : CoordinateSpace n =>
      (loadedRestrictedField ET FT ST k v).1) u =
      (loadedSlowCurrentFullLinear k).toContinuousLinearMap := by
    rw [hfun]
    exact hd.fderiv
  apply ContinuousLinearMap.ext
  intro s
  have hfst := hf.hasFDerivAt.fst.fderiv
  have hvalue := congrArg (fun L : CoordinateSpace n →L[ℝ] SlowSpace n =>
    L (s, (0 : FastSpace n))) (hfst.symm.trans hderiv)
  simpa [loadedBlockA, loadedSlowCurrentFullLinear] using hvalue

theorem loadedBlockB_eq_current {n : ℕ} (ET FT ST : ℝ)
    (k : Rates n) (u : CoordinateSpace n) :
    loadedBlockB ET FT ST k u =
      (loadedSlowCurrentLinear k).toContinuousLinearMap := by
  have hf := (differentiable_loadedRestrictedField ET FT ST k).differentiableAt
    (x := u)
  have hfun : (fun v : CoordinateSpace n =>
      (loadedRestrictedField ET FT ST k v).1) =
      loadedSlowCurrentFullLinear k := by
    funext v
    exact loadedRestrictedField_slow_eq_incidence_current ET FT ST k v
  have hd := (loadedSlowCurrentFullLinear k).toContinuousLinearMap.hasFDerivAt
    (x := u)
  have hderiv : fderiv ℝ (fun v : CoordinateSpace n =>
      (loadedRestrictedField ET FT ST k v).1) u =
      (loadedSlowCurrentFullLinear k).toContinuousLinearMap := by
    rw [hfun]
    exact hd.fderiv
  apply ContinuousLinearMap.ext
  intro f
  have hfst := hf.hasFDerivAt.fst.fderiv
  have hvalue := congrArg (fun L : CoordinateSpace n →L[ℝ] SlowSpace n =>
    L ((0 : SlowSpace n), f)) (hfst.symm.trans hderiv)
  simpa [loadedBlockB, loadedSlowCurrentFullLinear] using hvalue

/-- The source Schur matrix is the negative fast-mediated current response;
there is no direct slow-to-slow term in loaded coordinates. -/
theorem sourceSlowSchurMatrix_eq_current_response {n : ℕ}
    (ET FT ST : ℝ) (k : Rates n) (u : CoordinateSpace n) :
    sourceSlowSchurMatrix ET FT ST k u =
      -LinearMap.toMatrix (fastBasis n) (Pi.basisFun ℝ (Fin n))
        (loadedSlowCurrentLinear k) *
      (LinearMap.toMatrix (fastBasis n) (fastBasis n)
        (loadedBlockD ET FT ST k u).toLinearMap)⁻¹ *
      LinearMap.toMatrix (Pi.basisFun ℝ (Fin n)) (fastBasis n)
        (loadedBlockC ET FT ST k u).toLinearMap := by
  simp [sourceSlowSchurMatrix, loadedBlockA_eq_zero,
    loadedBlockB_eq_current]

/-- Current response after fast-complex elimination, before path incidence. -/
def sourceCurrentResponseMatrix {n : ℕ}
    (ET FT ST : ℝ) (k : Rates n) (u : CoordinateSpace n) :
    Matrix (Fin n) (Fin n) ℝ :=
  -LinearMap.toMatrix (fastBasis n) (Pi.basisFun ℝ (Fin n))
      (loadedCatalyticCurrentLinear k) *
    (LinearMap.toMatrix (fastBasis n) (fastBasis n)
      (loadedBlockD ET FT ST k u).toLinearMap)⁻¹ *
    LinearMap.toMatrix (Pi.basisFun ℝ (Fin n)) (fastBasis n)
      (loadedBlockC ET FT ST k u).toLinearMap

theorem sourceSlowSchurMatrix_eq_incidence_current_response {n : ℕ}
    (ET FT ST : ℝ) (k : Rates n) (u : CoordinateSpace n) :
    sourceSlowSchurMatrix ET FT ST k u =
      projectedPathIncidence n * sourceCurrentResponseMatrix ET FT ST k u := by
  rw [sourceSlowSchurMatrix_eq_current_response,
    loadedSlowCurrentLinear_toMatrix]
  simp [sourceCurrentResponseMatrix, Matrix.mul_assoc]

/-- Incidence does not change the determinant orientation. -/
theorem sourceSlowSchurMatrix_det_eq_current_response_det {n : ℕ}
    (ET FT ST : ℝ) (k : Rates n) (u : CoordinateSpace n) :
    (sourceSlowSchurMatrix ET FT ST k u).det =
      (sourceCurrentResponseMatrix ET FT ST k u).det := by
  rw [sourceSlowSchurMatrix_eq_incidence_current_response,
    Matrix.det_mul, projectedPathIncidence_det, one_mul]

/-- The exact attainment endpoint with its sole remaining source sign
input stated on the edge-current response rather than the Schur matrix. -/
theorem split_even_current_response_positive_attains
    (m : ℕ) (r τ δ ε : ℝ)
    (hr : 0 < r) (hτ : 0 < τ) (hε : 0 < ε)
    (hδ : 0 ≤ δ)
    (hD : DensePositive (splitRawD (m+1) r δ) (m+1))
    (hB : DensePositive (splitRawB (m+1) r δ) (m+1))
    (hadm : SplitRetunedFamilyAdmissible m r τ δ ε)
    (ρ : Fin (2*(m+1)+1) → ℝ)
    (hcert : ∀ j, SplitSlowModeCertificate m r τ δ ε j (ρ j))
    (hcurrent : ∀ i : Fin (m+2),
      0 < (-1 : ℝ)^(m+2) *
        (sourceCurrentResponseMatrix (2*r) 2 (2*(r+1))
          (splitFiniteRates (m+1) r δ)
          (loadedCoordOfState
            (splitFiniteState (m+1) r δ (splitEvenIndex m i)))).det) :
    LinearlyStableClassAttains (m+2) (m+2) := by
  apply split_even_schur_positive_attains
    m r τ δ ε hr hτ hε hδ hD hB hadm ρ hcert
  intro i
  rw [sourceSlowSchurMatrix_det_eq_current_response_det]
  exact hcurrent i

end
end PhosphorylationStableCapacity
