module
public import proofs.PhosphorylationStableCapacity.SplitDeterminantSlowSign
public import proofs.PhosphorylationStableCapacity.SplitRelaxDeterminant

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section

open PhosphorylationSharpness Matrix

/-- With an invertible fast block, the determinant of a real block
Jacobian is its fast determinant times the ordinary Schur determinant. -/
theorem real_block_det_schur_of_hurwitz
    {s f : Type*} [Fintype s] [Fintype f]
    [DecidableEq s] [DecidableEq f]
    (A : Matrix s s ℝ) (B : Matrix s f ℝ)
    (C : Matrix f s ℝ) (D : Matrix f f ℝ)
    (hD : IsHurwitz D) :
    (Matrix.fromBlocks A B C D).det =
      D.det * (A - B * D⁻¹ * C).det := by
  have hDunit : IsUnit D.det :=
    isUnit_iff_ne_zero.mpr (isHurwitz_det_ne_zero hD)
  have hInvertible : Invertible D :=
    Matrix.invertibleOfIsUnitDet D hDunit
  have hdet := @Matrix.det_fromBlocks₂₂ s f ℝ
    inferInstance inferInstance inferInstance inferInstance inferInstance
    A B C D hInvertible
  have hinv := @Matrix.invOf_eq_nonsing_inv f ℝ
    inferInstance inferInstance inferInstance D hInvertible
  simpa only [hinv] using hdet

/-- The actual unrelaxed source class Jacobian has a positive fast
determinant pivot. Its sign is therefore the sign of the reduced slow
Schur determinant. -/
theorem source_jacobian_det_eq_positive_fast_mul_schur {n : ℕ}
    (ET FT ST : ℝ) (k : Rates n) (u : CoordinateSpace n)
    (hk : k.Positive)
    (hpos : (stateFromLoaded ET FT ST u).Positive)
    (heq : Equilibrium k (stateFromLoaded ET FT ST u)) :
    let A := LinearMap.toMatrix (Pi.basisFun ℝ (Fin n))
      (Pi.basisFun ℝ (Fin n))
      (loadedBlockA ET FT ST k u).toLinearMap
    let B := LinearMap.toMatrix (fastBasis n)
      (Pi.basisFun ℝ (Fin n))
      (loadedBlockB ET FT ST k u).toLinearMap
    let C := LinearMap.toMatrix (Pi.basisFun ℝ (Fin n))
      (fastBasis n)
      (loadedBlockC ET FT ST k u).toLinearMap
    let D := LinearMap.toMatrix (fastBasis n) (fastBasis n)
      (loadedBlockD ET FT ST k u).toLinearMap
    0 < D.det ∧
      (restrictedJacobianMatrix ET FT ST k (fromLoadedCoord u)).det =
        D.det * (A - B * D⁻¹ * C).det := by
  dsimp only
  let A := LinearMap.toMatrix (Pi.basisFun ℝ (Fin n))
    (Pi.basisFun ℝ (Fin n))
    (loadedBlockA ET FT ST k u).toLinearMap
  let B := LinearMap.toMatrix (fastBasis n)
    (Pi.basisFun ℝ (Fin n))
    (loadedBlockB ET FT ST k u).toLinearMap
  let C := LinearMap.toMatrix (Pi.basisFun ℝ (Fin n))
    (fastBasis n)
    (loadedBlockC ET FT ST k u).toLinearMap
  let D := LinearMap.toMatrix (fastBasis n) (fastBasis n)
    (loadedBlockD ET FT ST k u).toLinearMap
  have hDpos : 0 < D.det :=
    loaded_source_fast_block_det_pos ET FT ST k u hk hpos heq
  let x := stateFromLoaded ET FT ST u
  let rho : Fin n → ℝ := fun i => k.a i*x.S i.castSucc*x.E
  let sigma : Fin n → ℝ := fun i => k.alpha i*x.S i.succ*x.F
  have hρ : ∀ i, 0 < rho i := by
    intro i
    exact mul_pos (mul_pos (hk i).1 (hpos.1 i.castSucc)) hpos.2.1
  have hσ : ∀ i, 0 < sigma i := by
    intro i
    exact mul_pos (mul_pos (hk i).2.2.2.1 (hpos.1 i.succ)) hpos.2.2.1
  have hDhurwitz : IsHurwitz D := by
    change IsHurwitz (LinearMap.toMatrix (fastBasis n) (fastBasis n)
      (loadedBlockD ET FT ST k u).toLinearMap)
    rw [loadedBlockD_toMatrix_eq_fastBinding ET FT ST k u hpos heq]
    exact fastBindingMatrix_hurwitz x hpos rho sigma hρ hσ
  refine ⟨hDpos, ?_⟩
  rw [restrictedJacobianMatrix_det_eq_loaded]
  rw [loadedJacobianMatrix_eq_fromBlocks]
  exact real_block_det_schur_of_hurwitz A B C D hDhurwitz

/-- The model-specific reduced slow matrix after eliminating the exact
positive fast complex-balance block. -/
def sourceSlowSchurMatrix {n : ℕ}
    (ET FT ST : ℝ) (k : Rates n) (u : CoordinateSpace n) :
    Matrix (Fin n) (Fin n) ℝ :=
  LinearMap.toMatrix (Pi.basisFun ℝ (Fin n))
      (Pi.basisFun ℝ (Fin n))
      (loadedBlockA ET FT ST k u).toLinearMap -
    LinearMap.toMatrix (fastBasis n)
      (Pi.basisFun ℝ (Fin n))
      (loadedBlockB ET FT ST k u).toLinearMap *
      (LinearMap.toMatrix (fastBasis n) (fastBasis n)
        (loadedBlockD ET FT ST k u).toLinearMap)⁻¹ *
      LinearMap.toMatrix (Pi.basisFun ℝ (Fin n))
        (fastBasis n)
        (loadedBlockC ET FT ST k u).toLinearMap

theorem source_jacobian_parity_det_sign_iff_schur {n : ℕ}
    (ET FT ST : ℝ) (k : Rates n) (u : CoordinateSpace n)
    (hk : k.Positive)
    (hpos : (stateFromLoaded ET FT ST u).Positive)
    (heq : Equilibrium k (stateFromLoaded ET FT ST u)) :
    0 < (-1 : ℝ)^n *
      (restrictedJacobianMatrix ET FT ST k (fromLoadedCoord u)).det ↔
    0 < (-1 : ℝ)^n *
      (sourceSlowSchurMatrix ET FT ST k u).det := by
  obtain ⟨hDpos, hfactor⟩ :=
    source_jacobian_det_eq_positive_fast_mul_schur
      ET FT ST k u hk hpos heq
  rw [hfactor]
  change 0 < (-1 : ℝ)^n *
      ((LinearMap.toMatrix (fastBasis n) (fastBasis n)
        (loadedBlockD ET FT ST k u).toLinearMap).det *
        (sourceSlowSchurMatrix ET FT ST k u).det) ↔
    0 < (-1 : ℝ)^n *
      (sourceSlowSchurMatrix ET FT ST k u).det
  rw [show (-1 : ℝ)^n *
      ((LinearMap.toMatrix (fastBasis n) (fastBasis n)
        (loadedBlockD ET FT ST k u).toLinearMap).det *
        (sourceSlowSchurMatrix ET FT ST k u).det) =
      (LinearMap.toMatrix (fastBasis n) (fastBasis n)
        (loadedBlockD ET FT ST k u).toLinearMap).det *
        ((-1 : ℝ)^n *
          (sourceSlowSchurMatrix ET FT ST k u).det) from by ring]
  exact mul_pos_iff_of_pos_left hDpos

/-- At each actual split source equilibrium, the only remaining
determinant sign is that of the `n × n` slow Schur matrix. -/
theorem split_source_jacobian_parity_det_sign_iff_schur
    (m : ℕ) (r δ : ℝ) (hδ : 0 ≤ δ)
    (hD : DensePositive (splitRawD (m+1) r δ) (m+1))
    (hB : DensePositive (splitRawB (m+1) r δ) (m+1))
    (j : Fin (2*(m+1)+1)) :
    let x := splitFiniteState (m+1) r δ j
    let u := loadedCoordOfState x
    0 < (-1 : ℝ)^(m+2) *
      (restrictedJacobianMatrix (2*r) 2 (2*(r+1))
        (splitFiniteRates (m+1) r δ)
        (toCoordinateSpace (chart x))).det ↔
    0 < (-1 : ℝ)^(m+2) *
      (sourceSlowSchurMatrix (2*r) 2 (2*(r+1))
        (splitFiniteRates (m+1) r δ) u).det := by
  dsimp only
  let x := splitFiniteState (m+1) r δ j
  let u := loadedCoordOfState x
  obtain ⟨hk, hpos, heq, hET, hFT, hST⟩ :=
    splitFiniteState_source_of_conversion_positive
      (m+1) r δ hδ hD hB j
  have hclass : InClass (2*r) 2 (2*(r+1)) x :=
    ⟨hET, hFT, hST⟩
  have hback : stateFromLoaded (2*r) 2 (2*(r+1)) u = x :=
    stateFromLoaded_loadedCoordOfState _ _ _ x hclass
  have hcoord : fromLoadedCoord u = toCoordinateSpace (chart x) := by
    simp [u, loadedCoordOfState, from_toLoadedCoord]
  have hsign := source_jacobian_parity_det_sign_iff_schur
    (2*r) 2 (2*(r+1)) (splitFiniteRates (m+1) r δ) u
    hk (by rw [hback]; exact hpos) (by rw [hback]; exact heq)
  rw [hcoord] at hsign
  exact hsign

/-- The verified chain now needs only a sign theorem for the `n × n`
source slow Schur matrix at the even-indexed roots to close attainment. -/
theorem split_even_schur_positive_attains
    (m : ℕ) (r τ δ ε : ℝ)
    (hr : 0 < r) (hτ : 0 < τ) (hε : 0 < ε)
    (hδ : 0 ≤ δ)
    (hD : DensePositive (splitRawD (m+1) r δ) (m+1))
    (hB : DensePositive (splitRawB (m+1) r δ) (m+1))
    (hadm : SplitRetunedFamilyAdmissible m r τ δ ε)
    (ρ : Fin (2*(m+1)+1) → ℝ)
    (hcert : ∀ j, SplitSlowModeCertificate m r τ δ ε j (ρ j))
    (hslow : ∀ i : Fin (m+2),
      0 < (-1 : ℝ)^(m+2) *
        (sourceSlowSchurMatrix (2*r) 2 (2*(r+1))
          (splitFiniteRates (m+1) r δ)
          (loadedCoordOfState
            (splitFiniteState (m+1) r δ (splitEvenIndex m i)))).det) :
    LinearlyStableClassAttains (m+2) (m+2) := by
  have hparity : (-1 : ℝ)^Fintype.card
      (Fin (m+2) ⊕ (Fin (m+2) ⊕ Fin (m+2))) =
      (-1 : ℝ)^(m+2) := by
    simp [Fintype.card_sum, pow_add]
    rcases neg_one_pow_eq_or ℝ m with h | h <;> simp [h]
  apply split_even_source_det_positive_attains
    m r τ δ ε hr hτ hε hadm ρ hcert
  intro i
  have hsign := split_source_jacobian_parity_det_sign_iff_schur
    m r δ hδ hD hB (splitEvenIndex m i)
  rw [hparity]
  exact hsign.mpr (hslow i)

end
end PhosphorylationStableCapacity
