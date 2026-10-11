module
public import proofs.PhosphorylationStableCapacity.SymmetricMatrixRowQuadraticBounds
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Prod

@[expose] public section

namespace PhosphorylationStableCapacity
noncomputable section
open Matrix
open scoped BigOperators

theorem symmetric_matrix_bilinear_swap {ι : Type*} [Fintype ι]
    (P : Matrix ι ι ℝ) (hP : P.IsSymm) (v w : ι → ℝ) :
    w ⬝ᵥ (P *ᵥ v) = v ⬝ᵥ (P *ᵥ w) := by
  simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  rw [hP.apply]
  ring

/-- Along an actual differentiable trajectory, the symmetric quadratic
energy has exactly the physical directional slope. -/
theorem symmetric_matrix_energy_hasDerivWithinAt
    {ι : Type*} [Fintype ι]
    (P : Matrix ι ι ℝ) (hP : P.IsSymm)
    (v : ℝ → ι → ℝ) (w : ι → ℝ) (s : Set ℝ) (t : ℝ)
    (hv : ∀ i, HasDerivWithinAt (fun r => v r i) (w i) s t) :
    HasDerivWithinAt (fun r => v r ⬝ᵥ (P *ᵥ v r))
      (2 * (v t ⬝ᵥ (P *ᵥ w))) s t := by
  have hsum : HasDerivWithinAt
      (fun r => ∑ i, ∑ j, v r i * (P i j * v r j))
      (∑ i, ∑ j, (w i * (P i j * v t j) + v t i * (P i j * w j))) s t := by
    apply HasDerivWithinAt.fun_sum
    intro i hi
    apply HasDerivWithinAt.fun_sum
    intro j hj
    exact (hv i).mul ((hv j).const_mul (P i j))
  have hvalue : (∑ i, ∑ j, (w i * (P i j * v t j) + v t i * (P i j * w j))) =
      2 * (v t ⬝ᵥ (P *ᵥ w)) := by
    simp only [Finset.sum_add_distrib]
    have hdot (a b : ι → ℝ) :
        (∑ i, ∑ j, a i * (P i j * b j)) = a ⬝ᵥ (P *ᵥ b) := by
      simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
    rw [hdot, hdot, symmetric_matrix_bilinear_swap P hP]
    ring
  rw [hvalue] at hsum
  simpa only [dotProduct, Matrix.mulVec, Finset.mul_sum] using hsum

end
end PhosphorylationStableCapacity
