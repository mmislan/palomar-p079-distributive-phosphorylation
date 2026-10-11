module
public import proofs.PhosphorylationStableCapacity.ArbitrarySplitDifferentiability

@[expose] public section
set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

namespace PhosphorylationStableCapacity

noncomputable section

open PhosphorylationSharpness Polynomial

/-- Bounded degree turns coefficientwise differentiability into
    differentiability of evaluation at a moving argument. -/
private theorem realCoeff_eval_differentiable
    (p : ℝ → ℝ[X]) (N : ℕ)
    (hp : RealCoeffDifferentiable p)
    (hdeg : ∀ δ, (p δ).natDegree < N)
    (u : ℝ → ℝ) (hu : Differentiable ℝ u) :
    Differentiable ℝ (fun δ => (p δ).eval (u δ)) := by
  have hsum : Differentiable ℝ (fun δ : ℝ =>
      ∑ i ∈ Finset.range N, (p δ).coeff i * (u δ)^i) := by
    apply Differentiable.fun_sum
    intro i hi
    exact (hp i).mul (hu.pow i)
  convert hsum using 1
  funext δ
  exact eval_eq_sum_range' (hdeg δ) (u δ)

theorem arbitrarySplitRawD_eval_differentiable
    (m : ℕ) (ξ : ℕ → ℝ) (r : ℝ) (hr : r ≠ 0)
    (u : ℝ → ℝ) (hu : Differentiable ℝ u) :
    Differentiable ℝ
      (fun δ => (arbitrarySplitRawD m ξ r δ).eval (u δ)) := by
  have hdeg (δ : ℝ) : (arbitrarySplitRawD m ξ r δ).natDegree < m+1 := by
    have hle := natDegree_le_iff_coeff_eq_zero.mpr
      (fun i hi => (arbitrarySplitRaw_coeff_zero_above m ξ r δ i hi).1)
    omega
  exact realCoeff_eval_differentiable _ (m+1)
    (fun i => arbitrarySplitRawD_coeff_differentiable m ξ r hr i)
    hdeg u hu

theorem arbitrarySplitRawB_eval_differentiable
    (m : ℕ) (ξ : ℕ → ℝ) (r : ℝ) (hr : r ≠ 0)
    (u : ℝ → ℝ) (hu : Differentiable ℝ u) :
    Differentiable ℝ
      (fun δ => (arbitrarySplitRawB m ξ r δ).eval (u δ)) := by
  have hdeg (δ : ℝ) : (arbitrarySplitRawB m ξ r δ).natDegree < m+1 := by
    have hle := natDegree_le_iff_coeff_eq_zero.mpr
      (fun i hi => (arbitrarySplitRaw_coeff_zero_above m ξ r δ i hi).2)
    omega
  exact realCoeff_eval_differentiable _ (m+1)
    (fun i => arbitrarySplitRawB_coeff_differentiable m ξ r hr i)
    hdeg u hu

theorem arbitrarySplitInventory_coeff_differentiable
    (m : ℕ) (ξ : ℕ → ℝ) (r : ℝ) (hr : r ≠ 0) (i : ℕ) :
    Differentiable ℝ (fun δ =>
      (((1 + Polynomial.X) * arbitrarySplitRawD m ξ r δ : ℝ[X]).coeff i)) := by
  have h : Differentiable ℝ (fun δ : ℝ =>
      ∑ ij ∈ Finset.HasAntidiagonal.antidiagonal i,
        ((1 + Polynomial.X : ℝ[X]).coeff ij.1) *
          (arbitrarySplitRawD m ξ r δ).coeff ij.2) := by
    apply Differentiable.fun_sum
    intro ij hij
    exact (differentiable_const _).mul
      (arbitrarySplitRawD_coeff_differentiable m ξ r hr ij.2)
  simpa only [Polynomial.coeff_mul] using h

end
end PhosphorylationStableCapacity
