module
public import proofs.PhosphorylationStableCapacity.FastSlowCharacteristicBlock

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section

open Matrix

/-- Multiplying the fast rows of the full characteristic matrix by
the nonzero time scale gives the polynomial block pencil. -/
theorem fastSlowCharacteristicBlock_eq_fast_row_scale
    {s f : Type*} [Fintype s] [Fintype f]
    [DecidableEq s] [DecidableEq f]
    (A : Matrix s s ℂ) (B : Matrix s f ℂ)
    (C : Matrix f s ℂ) (D : Matrix f f ℂ)
    (ε z : ℂ) (hε : ε ≠ 0) :
    fastSlowCharacteristicBlock A B C D ε z =
      Matrix.fromBlocks (1 : Matrix s s ℂ) 0 0 (ε • (1 : Matrix f f ℂ)) *
        (z • (1 : Matrix (s ⊕ f) (s ⊕ f) ℂ) -
          fastSlowMatrix A B C D ε) := by
  have hJ : z • (1 : Matrix (s ⊕ f) (s ⊕ f) ℂ) -
        fastSlowMatrix A B C D ε =
      Matrix.fromBlocks (z • 1 - A) (-B) (-(ε⁻¹ • C))
        (z • 1 - ε⁻¹ • D) := by
    ext i j
    cases i <;> cases j <;>
      simp [fastSlowMatrix, Matrix.one_apply, Matrix.sub_apply, Matrix.smul_apply,
        Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
        Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂]
  rw [hJ]
  simp [Matrix.fromBlocks_multiply]
  have hcancelL (x : ℂ) : ε⁻¹ * (ε * x) = x := by
    calc
      ε⁻¹ * (ε * x) = (ε⁻¹ * ε) * x := by ring
      _ = x := by simp [hε]
  ext i j
  cases i <;> cases j <;>
    simp [fastSlowCharacteristicBlock, Matrix.one_apply, Matrix.sub_apply,
      Matrix.smul_apply, Matrix.fromBlocks_apply₁₁,
      Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁,
      Matrix.fromBlocks_apply₂₂, hcancelL];
    simp [mul_sub, mul_ite, hε]

/-- The scaled block-pencil determinant differs from the full
characteristic determinant by exactly one factor of `ε` per fast row. -/
theorem fastSlowCharacteristicBlock_det_eq_fastSlowMatrix_det
    {s f : Type*} [Fintype s] [Fintype f]
    [DecidableEq s] [DecidableEq f]
    (A : Matrix s s ℂ) (B : Matrix s f ℂ)
    (C : Matrix f s ℂ) (D : Matrix f f ℂ)
    (ε z : ℂ) (hε : ε ≠ 0) :
    (fastSlowCharacteristicBlock A B C D ε z).det =
      ε ^ Fintype.card f *
        (z • (1 : Matrix (s ⊕ f) (s ⊕ f) ℂ) -
          fastSlowMatrix A B C D ε).det := by
  rw [fastSlowCharacteristicBlock_eq_fast_row_scale A B C D ε z hε,
    Matrix.det_mul, Matrix.det_fromBlocks_zero₂₁]
  simp

/-- The block pencil is exactly the characteristic polynomial of the
full Jacobian, multiplied by `ε` once per fast coordinate. -/
theorem fastSlowCharacteristicBlock_det_eq_charpoly
    {s f : Type*} [Fintype s] [Fintype f]
    [DecidableEq s] [DecidableEq f]
    (A : Matrix s s ℂ) (B : Matrix s f ℂ)
    (C : Matrix f s ℂ) (D : Matrix f f ℂ)
    (ε z : ℂ) (hε : ε ≠ 0) :
    (fastSlowCharacteristicBlock A B C D ε z).det =
      ε ^ Fintype.card f *
        (fastSlowMatrix A B C D ε).charpoly.eval z := by
  have hscalar : (Matrix.scalar (s ⊕ f) z :
      Matrix (s ⊕ f) (s ⊕ f) ℂ) = z • 1 := by
    ext i j
    by_cases hij : i = j <;> simp [Matrix.scalar_apply, hij]
  rw [fastSlowCharacteristicBlock_det_eq_fastSlowMatrix_det
    A B C D ε z hε, Matrix.eval_charpoly, hscalar]

/-- At spectral parameter zero the polynomial block pencil does not
depend on the binding time scale. -/
theorem fastSlowCharacteristicBlock_zero_spectral_parameter
    {s f : Type*} [Fintype s] [Fintype f]
    [DecidableEq s] [DecidableEq f]
    (A : Matrix s s ℂ) (B : Matrix s f ℂ)
    (C : Matrix f s ℂ) (D : Matrix f f ℂ) (ε : ℂ) :
    fastSlowCharacteristicBlock A B C D ε 0 =
      fastSlowCharacteristicBlock A B C D 0 0 := by
  simp [fastSlowCharacteristicBlock]

/-- A zero eigenvalue of the ordinary Schur matrix remains an exact
zero eigenvalue of every nonzero-scale full fast/slow matrix. -/
theorem fastSlowMatrix_zero_mem_spectrum_of_schur
    {s f : Type*} [Fintype s] [Fintype f]
    [DecidableEq s] [DecidableEq f]
    (A : Matrix s s ℂ) (B : Matrix s f ℂ)
    (C : Matrix f s ℂ) (D : Matrix f f ℂ)
    (hD : ∀ w : ℂ, w ∈ spectrum ℂ D → w.re < 0)
    (hS : (0 : ℂ) ∈ spectrum ℂ (A - B * D⁻¹ * C))
    (ε : ℂ) (hε : ε ≠ 0) :
    (0 : ℂ) ∈ spectrum ℂ (fastSlowMatrix A B C D ε) := by
  have hscalar : (Matrix.scalar s (0 : ℂ) : Matrix s s ℂ) =
      (0 : ℂ) • 1 := by
    ext i j
    by_cases hij : i = j <;> simp [Matrix.scalar_apply, hij]
  have hSdet : ((0 : ℂ) • (1 : Matrix s s ℂ) -
      (A - B * D⁻¹ * C)).det = 0 := by
    have hroot := Matrix.mem_spectrum_iff_isRoot_charpoly.mp hS
    simpa [Polynomial.IsRoot, Matrix.eval_charpoly, hscalar] using hroot
  have hpencil : (fastSlowCharacteristicBlock A B C D ε 0).det = 0 := by
    rw [fastSlowCharacteristicBlock_zero_spectral_parameter,
      fastSlowCharacteristicBlock_det_zero A B C D hD 0, hSdet, mul_zero]
  have hcharpoly : (fastSlowMatrix A B C D ε).charpoly.eval 0 = 0 := by
    rw [fastSlowCharacteristicBlock_det_eq_charpoly A B C D ε 0 hε]
      at hpencil
    exact (mul_eq_zero.mp hpencil).resolve_left (pow_ne_zero _ hε)
  exact Matrix.mem_spectrum_iff_isRoot_charpoly.mpr (by
    simpa [Polynomial.IsRoot] using hcharpoly)

end
end PhosphorylationStableCapacity
