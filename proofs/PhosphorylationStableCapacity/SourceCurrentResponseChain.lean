module
public import proofs.PhosphorylationStableCapacity.SourceFastTangentKernel
public import proofs.PhosphorylationStableCapacity.SourceCurrentSchur
public import proofs.PhosphorylationStableCapacity.SourceAugmentedCurrentOrientation

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section
open PhosphorylationSharpness Matrix

/-- An invertible fast block converts a zero fast tangent into the
current response after exact fast elimination. -/
theorem matrix_fast_response_action
    {s f : Type*} [Fintype s] [Fintype f]
    [DecidableEq s] [DecidableEq f]
    (V : Matrix s f ℝ) (C : Matrix f s ℝ) (D : Matrix f f ℝ)
    (hD : D.det ≠ 0) (a : s → ℝ) (b : f → ℝ) (z : s → ℝ)
    (hfast : C.mulVec a + D.mulVec b = 0)
    (hcurrent : V.mulVec b = z) :
    (-V * D⁻¹ * C).mulVec a = z := by
  have hunit : IsUnit D.det := isUnit_iff_ne_zero.mpr hD
  have hDb : D.mulVec b = -(C.mulVec a) := by
    ext i
    have hi := congrFun hfast i
    simp only [Pi.add_apply, Pi.zero_apply, Pi.neg_apply] at hi ⊢
    linarith
  have hb : b = -(D⁻¹.mulVec (C.mulVec a)) := by
    calc
      b = (D⁻¹ * D).mulVec b := by
        rw [Matrix.nonsing_inv_mul D hunit, Matrix.one_mulVec]
      _ = D⁻¹.mulVec (D.mulVec b) := by
        rw [Matrix.mulVec_mulVec]
      _ = -(D⁻¹.mulVec (C.mulVec a)) := by
        rw [hDb]
        rw [Matrix.mulVec_neg, Matrix.mulVec_mulVec]
  calc
    (-V * D⁻¹ * C).mulVec a =
        -V.mulVec (D⁻¹.mulVec (C.mulVec a)) := by
      simp only [Matrix.neg_mul, Matrix.neg_mulVec, Matrix.mulVec_mulVec,
        Matrix.mul_assoc]
    _ = V.mulVec b := by rw [hb, Matrix.mulVec_neg]
    _ = z := hcurrent

/-- The current component of the source binding tangent is the exact
derivative of each catalytic edge current in the fixed-total chart. -/
theorem equilibrium_sourceBindingTangent_current_action {n : ℕ}
    (k : Rates n) (x : State n)
    (hk : k.Positive) (hx : x.Positive)
    (heq : Equilibrium k x) (j : Fin n) :
    let A := (totalAndLevelOutputMatrix n) *
      loadedBindingMass x.S (sourceLevelC x) (sourceLevelD x)
        (totalE x) (totalF x)
    let σ := firstPivotFixedTangent A j
    let v := sourceBindingLoadedCoordinateTangent k x σ
    loadedCatalyticCurrentLinear k v.2 =
      (fun i => sourceConstrainedCurrentDerivative k x i j) := by
  dsimp only
  let A := (totalAndLevelOutputMatrix n) *
    loadedBindingMass x.S (sourceLevelC x) (sourceLevelD x)
      (totalE x) (totalF x)
  let σ := firstPivotFixedTangent A j
  let v := sourceBindingLoadedCoordinateTangent k x σ
  have h := equilibrium_sourceBindingTangent_loadedFderiv_action
    k x hk hx heq j
  dsimp only at h
  have hblock := loadedFderiv_block_action
    (totalE x) (totalF x) (totalS x) k
    (loadedCoordOfState x) v.1 v.2
  have hv : (v.1, v.2) = v := rfl
  rw [hv] at hblock
  have hslow := (congrArg Prod.fst hblock).symm.trans
    (congrArg Prod.fst h)
  have hslow' : (projectedPathIncidence n).mulVec
      (loadedCatalyticCurrentLinear k v.2) =
      (projectedPathIncidence n).mulVec
        (fun i => sourceConstrainedCurrentDerivative k x i j) := by
    simpa [loadedBlockA_eq_zero, loadedBlockB_eq_current,
      loadedSlowCurrentLinear] using hslow
  exact (Matrix.mulVec_injective_of_isUnit
    (projectedPathIncidence_isUnit n)) hslow'

/-- At a positive literal equilibrium, eliminating the fast block sends
each column of the constrained binding-mass derivative to the matching
column of the catalytic-current derivative. -/
theorem equilibrium_sourceCurrentResponse_constrainedMass_column {n : ℕ}
    (k : Rates n) (x : State n)
    (hk : k.Positive) (hx : x.Positive)
    (heq : Equilibrium k x) (j : Fin n) :
    (sourceCurrentResponseMatrix (totalE x) (totalF x) (totalS x)
      k (loadedCoordOfState x)).mulVec
        (fun i => sourceConstrainedBindingMass x i j) =
      (fun i => sourceConstrainedCurrentDerivative k x i j) := by
  let A := (totalAndLevelOutputMatrix n) *
    loadedBindingMass x.S (sourceLevelC x) (sourceLevelD x)
      (totalE x) (totalF x)
  let σ := firstPivotFixedTangent A j
  let v := sourceBindingLoadedCoordinateTangent k x σ
  let C := LinearMap.toMatrix (Pi.basisFun ℝ (Fin n)) (fastBasis n)
    (loadedBlockC (totalE x) (totalF x) (totalS x) k
      (loadedCoordOfState x)).toLinearMap
  let D := LinearMap.toMatrix (fastBasis n) (fastBasis n)
    (loadedBlockD (totalE x) (totalF x) (totalS x) k
      (loadedCoordOfState x)).toLinearMap
  let V := LinearMap.toMatrix (fastBasis n) (Pi.basisFun ℝ (Fin n))
    (loadedCatalyticCurrentLinear k)
  have hstate : stateFromLoaded (totalE x) (totalF x) (totalS x)
      (loadedCoordOfState x) = x := by
    exact stateFromLoaded_loadedCoordOfState
      (totalE x) (totalF x) (totalS x) x ⟨rfl, rfl, rfl⟩
  have hD : D.det ≠ 0 := by
    have h := loaded_source_fast_block_det_pos
      (totalE x) (totalF x) (totalS x) k
      (loadedCoordOfState x) hk (by simpa only [hstate] using hx)
      (by simpa only [hstate] using heq)
    exact ne_of_gt h
  have ha : v.1 = fun i => sourceConstrainedBindingMass x i j := by
    funext i
    calc
      v.1 i = (loadedBindingMass x.S (sourceLevelC x)
          (sourceLevelD x) (totalE x) (totalF x)).mulVec σ i.succ := rfl
      _ = A.mulVec σ i.succ := by
        have h := totalAndLevelOutputMatrix_mulVec_succ n
          ((loadedBindingMass x.S (sourceLevelC x)
            (sourceLevelD x) (totalE x) (totalF x)).mulVec σ) i
        simpa only [A, Matrix.mulVec_mulVec] using h.symm
      _ = sourceConstrainedBindingMass x i j := by
        simpa only [A, σ] using
          (sourceConstrainedBindingMass_eq_fixedTangent x i j).symm
  have hfast : C.mulVec v.1 +
      D.mulVec ((fastBasis n).repr v.2) = 0 := by
    have h := equilibrium_sourceBindingFastTangent_kernel
      k x hk hx heq j
    dsimp only at h
    have hr := congrArg (fastBasis n).repr h
    have hr' : (fastBasis n).repr
        (loadedBlockC (totalE x) (totalF x) (totalS x) k
          (loadedCoordOfState x) v.1) +
        (fastBasis n).repr
        (loadedBlockD (totalE x) (totalF x) (totalS x) k
          (loadedCoordOfState x) v.2) = 0 := by
      simpa only [A, σ, v, map_add, map_zero] using hr
    have hC : C.mulVec v.1 = (fastBasis n).repr
        (loadedBlockC (totalE x) (totalF x) (totalS x) k
          (loadedCoordOfState x) v.1) := by
      calc
        C.mulVec v.1 = C.mulVec ((Pi.basisFun ℝ (Fin n)).repr v.1) := by
          rfl
        _ = _ := by
          exact LinearMap.toMatrix_mulVec_repr
            (Pi.basisFun ℝ (Fin n)) (fastBasis n)
            (loadedBlockC (totalE x) (totalF x) (totalS x) k
              (loadedCoordOfState x)).toLinearMap v.1
    have hD' : D.mulVec ((fastBasis n).repr v.2) =
        (fastBasis n).repr
          (loadedBlockD (totalE x) (totalF x) (totalS x) k
            (loadedCoordOfState x) v.2) := by
      exact LinearMap.toMatrix_mulVec_repr
        (fastBasis n) (fastBasis n)
        (loadedBlockD (totalE x) (totalF x) (totalS x) k
          (loadedCoordOfState x)).toLinearMap v.2
    rw [hC, hD']
    funext i
    have hi := congrArg (fun w : (Fin n ⊕ Fin n) →₀ ℝ => w i) hr'
    simpa only [Pi.add_apply, Pi.zero_apply, Finsupp.add_apply,
      Finsupp.zero_apply] using hi
  have hcurrent : V.mulVec ((fastBasis n).repr v.2) =
      (fun i => sourceConstrainedCurrentDerivative k x i j) := by
    have h := equilibrium_sourceBindingTangent_current_action
      k x hk hx heq j
    dsimp only at h
    rw [LinearMap.toMatrix_mulVec_repr]
    rw [h]
    rfl
  have h := matrix_fast_response_action V C D hD v.1
    ((fastBasis n).repr v.2)
    (fun i => sourceConstrainedCurrentDerivative k x i j)
    hfast hcurrent
  simpa only [sourceCurrentResponseMatrix, V, C, D, ha] using h

/-- Exact source chain rule: current response in loaded coordinates,
times the positive binding mass of the fixed-total substrate chart,
equals the catalytic-current derivative on that substrate chart. -/
theorem equilibrium_sourceCurrentResponse_mul_constrainedMass {n : ℕ}
    (k : Rates n) (x : State n)
    (hk : k.Positive) (hx : x.Positive)
    (heq : Equilibrium k x) :
    sourceCurrentResponseMatrix (totalE x) (totalF x) (totalS x)
        k (loadedCoordOfState x) * sourceConstrainedBindingMass x =
      sourceConstrainedCurrentDerivative k x := by
  ext i j
  have h := equilibrium_sourceCurrentResponse_constrainedMass_column
    k x hk hx heq j
  exact congrFun h i

/-- The positive binding-mass coordinate change preserves the parity
orientation of the source current response. -/
theorem equilibrium_sourceCurrentResponse_parity_det_pos_iff {n : ℕ}
    (k : Rates n) (x : State n)
    (hk : k.Positive) (hx : x.Positive)
    (heq : Equilibrium k x) :
    0 < (-1 : ℝ)^n *
      (sourceCurrentResponseMatrix (totalE x) (totalF x) (totalS x)
        k (loadedCoordOfState x)).det ↔
    0 < (-1 : ℝ)^n *
      (sourceConstrainedCurrentDerivative k x).det := by
  let R := sourceCurrentResponseMatrix (totalE x) (totalF x)
    (totalS x) k (loadedCoordOfState x)
  let M := sourceConstrainedBindingMass x
  let J := sourceConstrainedCurrentDerivative k x
  have hdet : R.det * M.det = J.det := by
    rw [← Matrix.det_mul]
    exact congrArg Matrix.det
      (equilibrium_sourceCurrentResponse_mul_constrainedMass
        k x hk hx heq)
  have hm : 0 < M.det := sourceConstrainedBindingMass_det_pos x hx
  change 0 < (-1 : ℝ)^n * R.det ↔ 0 < (-1 : ℝ)^n * J.det
  rw [← hdet, ← mul_assoc]
  exact (mul_pos_iff_of_pos_right hm).symm

/-- The augmented physical total/current Jacobian and the exact loaded
current response have the same parity orientation at equilibrium. -/
theorem equilibrium_sourceCurrentResponse_augmented_parity_iff {n : ℕ}
    (k : Rates n) (x : State n)
    (hk : k.Positive) (hx : x.Positive)
    (heq : Equilibrium k x) :
    0 < (-1 : ℝ)^n *
      (sourceCurrentResponseMatrix (totalE x) (totalF x) (totalS x)
        k (loadedCoordOfState x)).det ↔
    0 < (-1 : ℝ)^n *
      (sourceAugmentedCurrentMatrix k x).det := by
  rw [equilibrium_sourceCurrentResponse_parity_det_pos_iff
    k x hk hx heq]
  exact (sourceAugmentedCurrentMatrix_parity_det_pos_iff k x hx).symm

/-- All verified spectral and source-coordinate steps reduce split-family
stable attainment to the sign of the explicit physical total/current
Jacobian at the even prescribed equilibria. -/
theorem split_even_augmented_current_positive_attains
    (m : ℕ) (r τ δ ε : ℝ)
    (hr : 0 < r) (hτ : 0 < τ) (hε : 0 < ε)
    (hδ : 0 ≤ δ)
    (hD : DensePositive (splitRawD (m+1) r δ) (m+1))
    (hB : DensePositive (splitRawB (m+1) r δ) (m+1))
    (hadm : SplitRetunedFamilyAdmissible m r τ δ ε)
    (ρ : Fin (2*(m+1)+1) → ℝ)
    (hcert : ∀ j, SplitSlowModeCertificate m r τ δ ε j (ρ j))
    (haug : ∀ i : Fin (m+2),
      0 < (-1 : ℝ)^(m+2) *
        (sourceAugmentedCurrentMatrix
          (splitFiniteRates (m+1) r δ)
          (splitFiniteState (m+1) r δ (splitEvenIndex m i))).det) :
    LinearlyStableClassAttains (m+2) (m+2) := by
  apply split_even_current_response_positive_attains
    m r τ δ ε hr hτ hε hδ hD hB hadm ρ hcert
  intro i
  let k := splitFiniteRates (m+1) r δ
  let x := splitFiniteState (m+1) r δ (splitEvenIndex m i)
  obtain ⟨hk, hx, heq, hET, hFT, hST⟩ :=
    splitFiniteState_source_of_conversion_positive
      (m+1) r δ hδ hD hB (splitEvenIndex m i)
  have hiff := equilibrium_sourceCurrentResponse_augmented_parity_iff
    k x hk hx heq
  simpa only [k, x, hET, hFT, hST] using hiff.mpr (haug i)

end
end PhosphorylationStableCapacity
