module
public import proofs.PhosphorylationStableCapacity.QuadraticMatrixTrajectory

@[expose] public section

namespace PhosphorylationStableCapacity
noncomputable section
open Matrix
open scoped BigOperators

theorem symmetric_matrix_lyapunov_directional_identity
    {ι : Type*} [Fintype ι] (A P : Matrix ι ι ℝ)
    (hP : P.IsSymm) (v : ι → ℝ) :
    v ⬝ᵥ ((A.transpose*P+P*A) *ᵥ v) =
      2*(v ⬝ᵥ (P *ᵥ (A *ᵥ v))) := by
  rw [Matrix.add_mulVec, dotProduct_add,
    ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    Matrix.dotProduct_transpose_mulVec]
  have hswap : (A *ᵥ v) ⬝ᵥ (P *ᵥ v) = v ⬝ᵥ (P *ᵥ (A *ᵥ v)) :=
    symmetric_matrix_bilinear_swap P hP v (A *ᵥ v)
  rw [dotProduct_comm (P *ᵥ v) (A *ᵥ v), hswap]
  ring

/-- A uniform absolute-row loss bound preserves quantitative dissipation
of the exact nominal decay matrix at every certified state. -/
theorem lyapunov_directional_le_of_row_loss
    {ι : Type*} [Fintype ι]
    (A P Q Δ : Matrix ι ι ℝ) (hP : P.IsSymm) (hΔ : Δ.IsSymm)
    (c₀ loss : ℝ)
    (hEq : A.transpose*P+P*A = -Q+Δ)
    (hQ : ∀ v : ι → ℝ, c₀*(∑ i, v i^2) ≤ v ⬝ᵥ (Q *ᵥ v))
    (hrows : ∀ i, (∑ j, |Δ i j|) ≤ loss) (v : ι → ℝ) :
    2*(v ⬝ᵥ (P *ᵥ (A *ᵥ v))) ≤ -(c₀-loss)*(∑ i, v i^2) := by
  have hdelta := symmetric_quadratic_le_of_rowBound Δ hΔ loss hrows v
  have hnominal := hQ v
  have hidentity := symmetric_matrix_lyapunov_directional_identity A P hP v
  rw [hEq, Matrix.add_mulVec, Matrix.neg_mulVec, dotProduct_add,
    dotProduct_neg] at hidentity
  nlinarith

theorem lyapunov_directional_energy_ratio
    {ι : Type*} [Fintype ι]
    (A P : Matrix ι ι ℝ) (v : ι → ℝ) (c M : ℝ)
    (hc : 0 ≤ c) (hM : 0 < M)
    (hslope : 2*(v ⬝ᵥ (P *ᵥ (A *ᵥ v))) ≤ -c*(∑ i, v i^2))
    (hupper : v ⬝ᵥ (P *ᵥ v) ≤ M*(∑ i, v i^2)) :
    2*(v ⬝ᵥ (P *ᵥ (A *ᵥ v))) ≤ -(c/M)*(v ⬝ᵥ (P *ᵥ v)) := by
  have hscaled := mul_le_mul_of_nonneg_left hupper (div_nonneg hc hM.le)
  have hcancel : (c/M)*(M*(∑ i, v i^2)) = c*(∑ i, v i^2) := by
    rw [← mul_assoc, div_mul_cancel₀ c (ne_of_gt hM)]
  rw [hcancel] at hscaled
  nlinarith

end
end PhosphorylationStableCapacity
