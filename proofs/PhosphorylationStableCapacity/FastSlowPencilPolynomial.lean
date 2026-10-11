module
public import proofs.PhosphorylationStableCapacity.FastSlowCharacteristicPositive

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section

open Matrix Polynomial

/-- The block-pencil determinant as a polynomial in the spectral
parameter. Its matrix coefficients are polynomial in the time scale. -/
def fastSlowPencilPolynomial
    {s f : Type*} [Fintype s] [Fintype f]
    [DecidableEq s] [DecidableEq f]
    (A : Matrix s s ℂ) (B : Matrix s f ℂ)
    (C : Matrix f s ℂ) (D : Matrix f f ℂ) (ε : ℂ) : ℂ[X] :=
  let M₀ : Matrix (s ⊕ f) (s ⊕ f) ℂ :=
    Matrix.fromBlocks (-A) (-B) (-C) (-D)
  let M₁ : Matrix (s ⊕ f) (s ⊕ f) ℂ :=
    Matrix.fromBlocks (1 : Matrix s s ℂ) 0 0
    (ε • (1 : Matrix f f ℂ))
  (M₀.map Polynomial.C + (Polynomial.X : ℂ[X]) • M₁.map Polynomial.C).det

/-- The pencil has a binding-scale-independent degree bound in the
spectral parameter, even though its leading coefficient vanishes at
zero binding scale. -/
theorem fastSlowPencilPolynomial_natDegree_le
    {s f : Type*} [Fintype s] [Fintype f]
    [DecidableEq s] [DecidableEq f]
    (A : Matrix s s ℂ) (B : Matrix s f ℂ)
    (C : Matrix f s ℂ) (D : Matrix f f ℂ) (ε : ℂ) :
    (fastSlowPencilPolynomial A B C D ε).natDegree ≤
      Fintype.card (s ⊕ f) := by
  let M₀ : Matrix (s ⊕ f) (s ⊕ f) ℂ :=
    Matrix.fromBlocks (-A) (-B) (-C) (-D)
  let M₁ : Matrix (s ⊕ f) (s ⊕ f) ℂ :=
    Matrix.fromBlocks (1 : Matrix s s ℂ) 0 0
      (ε • (1 : Matrix f f ℂ))
  have h := Polynomial.natDegree_det_X_add_C_le M₁ M₀
  simpa only [fastSlowPencilPolynomial, ← add_comm] using h

/-- Evaluating the polynomial pencil gives the previously defined
block characteristic determinant. -/
theorem fastSlowPencilPolynomial_eval
    {s f : Type*} [Fintype s] [Fintype f]
    [DecidableEq s] [DecidableEq f]
    (A : Matrix s s ℂ) (B : Matrix s f ℂ)
    (C : Matrix f s ℂ) (D : Matrix f f ℂ) (ε z : ℂ) :
    (fastSlowPencilPolynomial A B C D ε).eval z =
      (fastSlowCharacteristicBlock A B C D ε z).det := by
  rw [fastSlowPencilPolynomial, ← Polynomial.coe_evalRingHom,
    RingHom.map_det]
  congr 1
  ext i j
  cases i <;> cases j <;>
    simp [fastSlowCharacteristicBlock, Matrix.fromBlocks_apply₁₁,
      Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁,
      Matrix.fromBlocks_apply₂₂, Matrix.smul_apply,
      Matrix.add_apply, Matrix.map_apply, Matrix.one_apply] <;>
    (split_ifs <;> (try simp [Polynomial.eval_X]); ring)

/-- At zero binding time scale, the entire polynomial pencil factors as
the fast determinant times the ordinary Schur characteristic polynomial. -/
theorem fastSlowPencilPolynomial_zero_eq
    {s f : Type*} [Fintype s] [Fintype f]
    [DecidableEq s] [DecidableEq f]
    (A : Matrix s s ℂ) (B : Matrix s f ℂ)
    (C : Matrix f s ℂ) (D : Matrix f f ℂ)
    (hD : ∀ w : ℂ, w ∈ spectrum ℂ D → w.re < 0) :
    fastSlowPencilPolynomial A B C D 0 =
      Polynomial.C (-D).det * (A - B * D⁻¹ * C).charpoly := by
  apply Polynomial.funext
  intro z
  have hscalar : (Matrix.scalar s z : Matrix s s ℂ) = z • 1 := by
    ext i j
    by_cases hij : i = j <;> simp [Matrix.scalar_apply, hij]
  rw [fastSlowPencilPolynomial_eval,
    fastSlowCharacteristicBlock_det_zero A B C D hD z,
    Polynomial.eval_mul, Polynomial.eval_C,
    Matrix.eval_charpoly, hscalar]

/-- A simple zero of the ordinary Schur characteristic polynomial gives
a nonzero linear coefficient of the zero-scale block pencil. -/
theorem fastSlowPencilPolynomial_zero_coeff_one_ne_zero
    {s f : Type*} [Fintype s] [Fintype f]
    [DecidableEq s] [DecidableEq f]
    (A : Matrix s s ℂ) (B : Matrix s f ℂ)
    (C : Matrix f s ℂ) (D : Matrix f f ℂ)
    (hD : ∀ w : ℂ, w ∈ spectrum ℂ D → w.re < 0)
    (q : ℂ[X])
    (hS : (A - B * D⁻¹ * C).charpoly = q * Polynomial.X)
    (hq : q.eval 0 ≠ 0) :
    (fastSlowPencilPolynomial A B C D 0).coeff 1 ≠ 0 := by
  have hunit : IsUnit (-D).det := by
    simpa [fastSlowResolventMatrix] using
      (fastSlowResolventMatrix_isUnit_det_of_hurwitz D hD
        (show (0 : ℝ) < 1 by norm_num) 0 (le_refl 0))
  rw [fastSlowPencilPolynomial_zero_eq A B C D hD, hS]
  have hfactor : Polynomial.C (-D).det * (q * Polynomial.X) =
      Polynomial.X * (Polynomial.C (-D).det * q) := by ring
  rw [hfactor, Polynomial.coeff_X_mul, Polynomial.mul_coeff_zero,
    Polynomial.coeff_C_zero]
  exact mul_ne_zero hunit.ne_zero (by simpa [Polynomial.coeff_zero_eq_eval_zero] using hq)

/-- A Schur zero produces an exact `X` factor of the block-pencil
polynomial at every binding scale, including zero scale. -/
theorem fastSlowPencilPolynomial_X_factor
    {s f : Type*} [Fintype s] [Fintype f]
    [DecidableEq s] [DecidableEq f]
    (A : Matrix s s ℂ) (B : Matrix s f ℂ)
    (C : Matrix f s ℂ) (D : Matrix f f ℂ)
    (hD : ∀ w : ℂ, w ∈ spectrum ℂ D → w.re < 0)
    (hS : (0 : ℂ) ∈ spectrum ℂ (A - B * D⁻¹ * C))
    (ε : ℂ) :
    fastSlowPencilPolynomial A B C D ε =
      Polynomial.X * (fastSlowPencilPolynomial A B C D ε).divX := by
  have hzero : (fastSlowPencilPolynomial A B C D ε).coeff 0 = 0 := by
    rw [Polynomial.coeff_zero_eq_eval_zero,
      fastSlowPencilPolynomial_eval,
      fastSlowCharacteristicBlock_zero_spectral_parameter,
      fastSlowCharacteristicBlock_det_zero A B C D hD 0]
    have hroot := Matrix.mem_spectrum_iff_isRoot_charpoly.mp hS
    have hscalar : (Matrix.scalar s (0 : ℂ) : Matrix s s ℂ) =
        (0 : ℂ) • 1 := by
      ext i j
      by_cases hij : i = j <;> simp [Matrix.scalar_apply, hij]
    have hdet : (0 • (1 : Matrix s s ℂ) -
        (A - B * D⁻¹ * C)).det = 0 := by
      simpa [Polynomial.IsRoot, Matrix.eval_charpoly, hscalar] using hroot
    exact mul_eq_zero.mpr (Or.inr (by simpa using hdet))
  have h := Polynomial.X_mul_divX_add (fastSlowPencilPolynomial A B C D ε)
  simpa [hzero] using h.symm

end
end PhosphorylationStableCapacity
