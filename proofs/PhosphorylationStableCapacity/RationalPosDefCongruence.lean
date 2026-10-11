module
public import Mathlib.LinearAlgebra.QuadraticForm.Basic
public import Mathlib.LinearAlgebra.Matrix.BilinearForm
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.Tactic.NoncommRing

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section

/-- A positive definite rational matrix admits an exact rational diagonal
congruence certificate.  The certificate used by the P079 LDL checker does
not impose a triangular shape on `L`; an orthogonal basis over `ℚ` is enough.
The matrix `R` is a right inverse, so every diagonal factor is essential. -/
theorem rational_posDef_has_congruence_factor {ι : Type*}
    [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι ℚ) (hM : M.PosDef) :
    ∃ (L R : Matrix ι ι ℚ) (d : ι → ℚ),
      (∀ i, 0 < d i) ∧ L * R = 1 ∧
        M = L * Matrix.diagonal d * L.transpose := by
  classical
  let std : Module.Basis ι ℚ (ι → ℚ) := Pi.basisFun ℚ ι
  let B : LinearMap.BilinForm ℚ (ι → ℚ) := Matrix.toBilin' M
  have hstd : LinearMap.toMatrix₂ std std B = M := by
    change LinearMap.toMatrix₂ (Pi.basisFun ℚ ι) (Pi.basisFun ℚ ι)
      (Matrix.toBilin' M) = M
    rw [LinearMap.toMatrix₂_basisFun]
    exact LinearMap.BilinForm.toMatrix'_toBilin' M
  have hsym : B.IsSymm := by
    exact Matrix.isSymm_toBilin'_iff_isSymm.mpr hM.1.isSymm
  obtain ⟨v₀, hv₀⟩ :=
    LinearMap.BilinForm.exists_orthogonal_basis (LinearMap.BilinForm.isSymm_iff.mp hsym)
  have hdim : Module.finrank ℚ (ι → ℚ) = Fintype.card ι :=
    Module.finrank_fintype_fun_eq_card ℚ
  let e : Fin (Module.finrank ℚ (ι → ℚ)) ≃ ι :=
    (finCongr hdim).trans (Fintype.equivFin ι).symm
  let v : Module.Basis ι ℚ (ι → ℚ) := v₀.reindex e
  have hv : B.IsOrthoᵢ v := by
    intro i j hij
    change B (v i) (v j) = 0
    simpa only [v, Module.Basis.reindex_apply] using
      (hv₀ (fun heq => hij (e.symm.injective heq)))
  let d : ι → ℚ := fun i => B (v i) (v i)
  have hd (i : ι) : 0 < d i := by
    have hvi : (v i : ι → ℚ) ≠ 0 := v.ne_zero i
    have hp := hM.dotProduct_mulVec_pos hvi
    simpa only [d, B, Matrix.toBilin'_apply', star_trivial] using hp
  have hdiag :
      LinearMap.toMatrix₂ v v B = Matrix.diagonal d := by
    ext i j
    rw [LinearMap.toMatrix₂_apply]
    by_cases hij : i = j
    · subst j
      rw [Matrix.diagonal_apply_eq]
    · rw [Matrix.diagonal_apply_ne d hij]
      exact hv hij
  let U : Matrix ι ι ℚ := std.toMatrix v
  let R : Matrix ι ι ℚ := v.toMatrix std
  have hUR : U * R = 1 := by
    simpa only [U, R] using std.toMatrix_mul_toMatrix_flip v
  have hURt : R.transpose * U.transpose = 1 := by
    simpa only [Matrix.transpose_mul, Matrix.transpose_one] using
      congrArg Matrix.transpose hUR
  have hconj : U.transpose * M * U = Matrix.diagonal d := by
    have hchange := LinearMap.toMatrix₂_mul_basis_toMatrix
      (b₁ := std) (b₂ := std) v v B
    rw [hstd, hdiag] at hchange
    exact hchange
  have hfactor : M = R.transpose * Matrix.diagonal d * R := by
    calc
      M = (R.transpose * U.transpose) * M * (U * R) := by
        rw [hURt, hUR]
        simp
      _ = R.transpose * (U.transpose * M * U) * R := by
        noncomm_ring
      _ = R.transpose * Matrix.diagonal d * R := by
        rw [hconj]
  refine ⟨R.transpose, U.transpose, d, hd, hURt, ?_⟩
  simpa only [Matrix.transpose_transpose] using hfactor

end
end PhosphorylationStableCapacity
