module
public import proofs.PhosphorylationStableCapacity.LoadedJacobianCharpolyBridge
public import proofs.PhosphorylationStableCapacity.SplitConversionResidual

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section

open PhosphorylationSharpness Matrix

/-- Positive binding relaxation scales the full determinant by a positive
even power; the statement is purely a row-scaling identity. -/
theorem realFastSlowMatrix_det
    {s f : Type*} [Fintype s] [Fintype f]
    [DecidableEq s] [DecidableEq f]
    (A : Matrix s s ℝ) (B : Matrix s f ℝ)
    (C : Matrix f s ℝ) (D : Matrix f f ℝ) (ε : ℝ) :
    (realFastSlowMatrix A B C D ε).det =
      (ε⁻¹) ^ Fintype.card f * (Matrix.fromBlocks A B C D).det := by
  let v : s ⊕ f → ℝ := Sum.elim (fun _ => 1) (fun _ => ε⁻¹)
  have hmatrix : realFastSlowMatrix A B C D ε =
      Matrix.of (fun i j => v i * (Matrix.fromBlocks A B C D) i j) := by
    ext i j
    cases i <;> cases j <;>
      simp [realFastSlowMatrix, v, Matrix.fromBlocks_apply₁₁,
        Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁,
        Matrix.fromBlocks_apply₂₂, Matrix.smul_apply]
  rw [hmatrix, Matrix.det_mul_column]
  simp [v, Fintype.prod_sum_type, Finset.prod_const, Finset.card_univ]

theorem loadedJacobianMatrix_relax_det {n : ℕ}
    (ET FT ST : ℝ) (k : Rates n) (u : CoordinateSpace n)
    {ε : ℝ} (hε : ε ≠ 0) :
    (loadedJacobianMatrix ET FT ST (relaxRates k ε) u).det =
      (ε⁻¹) ^ (2*n) * (loadedJacobianMatrix ET FT ST k u).det := by
  rw [loadedJacobianMatrix_relax_eq_realFastSlow ET FT ST k u hε,
    realFastSlowMatrix_det, loadedJacobianMatrix_eq_fromBlocks]
  simp only [Fintype.card_sum, Fintype.card_fin]
  ring

theorem restrictedJacobianMatrix_det_eq_loaded {n : ℕ}
    (ET FT ST : ℝ) (k : Rates n) (u : CoordinateSpace n) :
    (restrictedJacobianMatrix ET FT ST k (fromLoadedCoord u)).det =
      (loadedJacobianMatrix ET FT ST k u).det := by
  rw [Matrix.det_eq_sign_charpoly_coeff,
    Matrix.det_eq_sign_charpoly_coeff,
    loadedJacobianMatrix_charpoly_eq_restricted]

/-- Binding relaxation preserves the sign of the literal class-Jacobian
determinant at every state and every positive relaxation parameter. -/
theorem restrictedJacobianMatrix_relax_det {n : ℕ}
    (ET FT ST : ℝ) (k : Rates n) (u : CoordinateSpace n)
    {ε : ℝ} (hε : 0 < ε) :
    (restrictedJacobianMatrix ET FT ST (relaxRates k ε)
      (fromLoadedCoord u)).det =
      (ε⁻¹) ^ (2*n) *
        (restrictedJacobianMatrix ET FT ST k (fromLoadedCoord u)).det := by
  rw [restrictedJacobianMatrix_det_eq_loaded,
    restrictedJacobianMatrix_det_eq_loaded,
    loadedJacobianMatrix_relax_det ET FT ST k u (ne_of_gt hε)]

theorem restrictedJacobianMatrix_relax_det_sign {n : ℕ}
    (ET FT ST : ℝ) (k : Rates n) (u : CoordinateSpace n)
    {ε : ℝ} (hε : 0 < ε) :
    ((restrictedJacobianMatrix ET FT ST (relaxRates k ε)
        (fromLoadedCoord u)).det < 0 ↔
      (restrictedJacobianMatrix ET FT ST k (fromLoadedCoord u)).det < 0) ∧
    (0 < (restrictedJacobianMatrix ET FT ST (relaxRates k ε)
        (fromLoadedCoord u)).det ↔
      0 < (restrictedJacobianMatrix ET FT ST k (fromLoadedCoord u)).det) := by
  rw [restrictedJacobianMatrix_relax_det ET FT ST k u hε]
  have hfac : 0 < (ε⁻¹) ^ (2*n) := pow_pos (inv_pos.mpr hε) _
  constructor
  · simpa using (mul_lt_mul_iff_of_pos_left hfac (b :=
      (restrictedJacobianMatrix ET FT ST k (fromLoadedCoord u)).det)
      (c := 0))
  · exact mul_pos_iff_of_pos_left hfac

end
end PhosphorylationStableCapacity
