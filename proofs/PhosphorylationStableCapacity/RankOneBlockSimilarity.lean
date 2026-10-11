module
public import proofs.PhosphorylationStableCapacity.RankOneMetzlerPerturbation

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A block matrix whose final column is scaled by `τ`. -/
def finalColumnWeightedBlocks
    (A : Matrix ι ι ℝ) (B : Matrix ι (Fin 1) ℝ)
    (C : Matrix (Fin 1) ι ℝ) (D : Matrix (Fin 1) (Fin 1) ℝ)
    (τ : ℝ) : Matrix (ι ⊕ Fin 1) (ι ⊕ Fin 1) ℝ :=
  Matrix.fromBlocks A (τ • B) C (τ • D)

/-- The triangular change of basis whose final column is a normalized
zero mode at final current weight `τ`. -/
def finalColumnShear (U : Matrix ι (Fin 1) ℝ) (τ : ℝ) :
    Matrix (ι ⊕ Fin 1) (ι ⊕ Fin 1) ℝ :=
  Matrix.fromBlocks 1 (τ • U) 0 1

def finalColumnShearInv (U : Matrix ι (Fin 1) ℝ) (τ : ℝ) :
    Matrix (ι ⊕ Fin 1) (ι ⊕ Fin 1) ℝ :=
  Matrix.fromBlocks 1 (-(τ • U)) 0 1

theorem finalColumnShearInv_mul (U : Matrix ι (Fin 1) ℝ) (τ : ℝ) :
    finalColumnShearInv U τ * finalColumnShear U τ = 1 := by
  simp [finalColumnShearInv, finalColumnShear,
    Matrix.fromBlocks_multiply, ← Matrix.fromBlocks_one]

theorem finalColumnShear_mul_inv (U : Matrix ι (Fin 1) ℝ) (τ : ℝ) :
    finalColumnShear U τ * finalColumnShearInv U τ = 1 := by
  simp [finalColumnShearInv, finalColumnShear,
    Matrix.fromBlocks_multiply, ← Matrix.fromBlocks_one]

/-- A normalized zero mode turns the final-column-weighted matrix into a
block lower triangular matrix by an exact triangular similarity. -/
theorem finalColumnWeightedBlocks_shear
    (A : Matrix ι ι ℝ) (B : Matrix ι (Fin 1) ℝ)
    (C : Matrix (Fin 1) ι ℝ) (D : Matrix (Fin 1) (Fin 1) ℝ)
    (U : Matrix ι (Fin 1) ℝ) (τ : ℝ)
    (hAU : A * U + B = 0) (hCU : C * U + D = 0) :
    finalColumnShearInv U τ * finalColumnWeightedBlocks A B C D τ *
      finalColumnShear U τ =
        Matrix.fromBlocks (A - τ • (U * C)) 0 C 0 := by
  have hWT : finalColumnWeightedBlocks A B C D τ *
      finalColumnShear U τ = Matrix.fromBlocks A 0 C 0 := by
    simp [finalColumnWeightedBlocks, finalColumnShear,
      Matrix.fromBlocks_multiply, ← smul_add, hAU, hCU]
  rw [mul_assoc, hWT]
  simp [finalColumnShearInv, Matrix.fromBlocks_multiply,
    Matrix.smul_mul, sub_eq_add_neg]

/-- The exact characteristic polynomial has one explicit zero factor; the
other factor is the rank-one complementary block. -/
theorem finalColumnWeightedBlocks_charpoly
    (A : Matrix ι ι ℝ) (B : Matrix ι (Fin 1) ℝ)
    (C : Matrix (Fin 1) ι ℝ) (D : Matrix (Fin 1) (Fin 1) ℝ)
    (U : Matrix ι (Fin 1) ℝ) (τ : ℝ)
    (hAU : A * U + B = 0) (hCU : C * U + D = 0) :
    (finalColumnWeightedBlocks A B C D τ).charpoly =
      (A - τ • (U * C)).charpoly * Polynomial.X := by
  have hchar :
      (finalColumnShearInv U τ *
        finalColumnWeightedBlocks A B C D τ *
          finalColumnShear U τ).charpoly =
        (finalColumnWeightedBlocks A B C D τ).charpoly := by
    rw [Matrix.charpoly_mul_comm]
    rw [← mul_assoc, finalColumnShear_mul_inv, one_mul]
  rw [finalColumnWeightedBlocks_shear A B C D U τ hAU hCU] at hchar
  simpa using hchar.symm

end
end PhosphorylationStableCapacity
