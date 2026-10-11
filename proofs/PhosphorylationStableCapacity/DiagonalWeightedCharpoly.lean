module
public import Mathlib.Basic.Real.Basic
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
public import Mathlib.Data.Matrix.Mul

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section
open Matrix

/-- Positive coordinate scaling does not change the characteristic polynomial.
Only nonzero scales are needed for this algebraic statement. -/
theorem diagonal_weighted_charpoly
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (s : ι → ℝ) (hs : ∀ i, s i ≠ 0) :
    (Matrix.of fun i j => A i j * s j / s i).charpoly = A.charpoly := by
  let D : Matrix ι ι ℝ := diagonal s
  let E : Matrix ι ι ℝ := diagonal (fun i => (s i)⁻¹)
  have hDE : D * E = 1 := by
    ext i j
    simp only [D, E, diagonal_mul_diagonal]
    by_cases hij : i = j
    · subst j
      simp [hs i]
    · simp [hij]
  have hweighted : (Matrix.of fun i j => A i j * s j / s i) = E * A * D := by
    ext i j
    simp [E, D, div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm]
  rw [hweighted]
  calc
    (E * A * D).charpoly = (D * (E * A)).charpoly :=
      Matrix.charpoly_mul_comm (E * A) D
    _ = A.charpoly := by rw [← mul_assoc, hDE, one_mul]

end
end PhosphorylationStableCapacity
