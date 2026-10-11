module
public import Mathlib.LinearAlgebra.Matrix.Block
public import Mathlib.Algebra.Order.Ring.Int
public import Mathlib.Data.Fintype.Fin

@[expose] public section

namespace PhosphorylationStableCapacity

open scoped BigOperators

/-- An exact triangular multiplication certificate proves the sign of the
original integer determinant without expanding its permutation formula. -/
theorem integer_det_pos_of_triangular_product
    {n : ℕ} (A E T : Matrix (Fin n) (Fin n) ℤ)
    (hE : E.IsLowerTriangular) (hT : T.IsUpperTriangular)
    (hproduct : E * A = T)
    (hdiagE : 0 < ∏ i : Fin n, E i i)
    (hdiagT : 0 < ∏ i : Fin n, T i i) :
    0 < A.det := by
  have he : 0 < E.det := by
    rw [Matrix.det_of_isLowerTriangular E hE]
    exact hdiagE
  have ht : 0 < T.det := by
    rw [Matrix.det_of_isUpperTriangular hT]
    exact hdiagT
  have hmul : 0 < E.det * A.det := by
    rw [← Matrix.det_mul, hproduct]
    exact ht
  exact pos_of_mul_pos_right hmul he.le

end PhosphorylationStableCapacity
