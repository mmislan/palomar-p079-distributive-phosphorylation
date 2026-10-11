module
public import proofs.PhosphorylationStableCapacity.FastBindingRateDiagonal

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section
open PhosphorylationSharpness
open Matrix

theorem fastRateWeights_pos {n : ℕ} (rho sigma : Fin n → ℝ)
    (hρ : ∀ i, 0 < rho i) (hσ : ∀ i, 0 < sigma i)
    (a : Fin n ⊕ Fin n) : 0 < fastRateWeights n rho sigma a := by
  cases a with
  | inl i => exact hρ i
  | inr i => exact hσ i

def fastSqrtRateMatrix (n : ℕ) (rho sigma : Fin n → ℝ) :
    Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ :=
  Matrix.diagonal (fun a => Real.sqrt (fastRateWeights n rho sigma a))

theorem fastSqrtRateMatrix_sq {n : ℕ} (rho sigma : Fin n → ℝ)
    (hρ : ∀ i, 0 < rho i) (hσ : ∀ i, 0 < sigma i) :
    fastSqrtRateMatrix n rho sigma * fastSqrtRateMatrix n rho sigma =
      fastRateMatrix n rho sigma := by
  classical
  rw [fastRateMatrix_eq_diagonal]
  simp only [fastSqrtRateMatrix, Matrix.diagonal_mul_diagonal]
  congr 1
  funext a
  exact Real.mul_self_sqrt (fastRateWeights_pos rho sigma hρ hσ a).le

theorem fastSqrtRateMatrix_isHermitian {n : ℕ}
    (rho sigma : Fin n → ℝ) :
    (fastSqrtRateMatrix n rho sigma).IsHermitian := by
  classical
  exact Matrix.isHermitian_diagonal _

theorem fastSqrtRateMatrix_mulVec_injective {n : ℕ}
    (rho sigma : Fin n → ℝ)
    (hρ : ∀ i, 0 < rho i) (hσ : ∀ i, 0 < sigma i) :
    Function.Injective (fastSqrtRateMatrix n rho sigma).mulVec := by
  intro u v h
  funext a
  have ha := congrArg (fun z : Fin n ⊕ Fin n → ℝ => z a) h
  simp only [fastSqrtRateMatrix, Matrix.mulVec_diagonal] at ha
  exact (mul_left_cancel₀
    (ne_of_gt (Real.sqrt_pos.2 (fastRateWeights_pos rho sigma hρ hσ a)))) ha

def fastSymmetricBindingMatrix (n : ℕ) (x : State n)
    (rho sigma : Fin n → ℝ) :
    Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ :=
  (fastSqrtRateMatrix n rho sigma)ᴴ *
    fastAffinityMatrix n x * fastSqrtRateMatrix n rho sigma

theorem fastSymmetricBindingMatrix_posDef {n : ℕ} (x : State n)
    (hx : x.Positive) (rho sigma : Fin n → ℝ)
    (hρ : ∀ i, 0 < rho i) (hσ : ∀ i, 0 < sigma i) :
    (fastSymmetricBindingMatrix n x rho sigma).PosDef := by
  exact (fastAffinityMatrix_posDef x hx).conjTranspose_mul_mul_same
    (fastSqrtRateMatrix_mulVec_injective rho sigma hρ hσ)

end
end PhosphorylationStableCapacity
