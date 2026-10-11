module
public import proofs.PhosphorylationStableCapacity.Jacobian
public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.LinearAlgebra.Basis.Defs

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section

open PhosphorylationSharpness Matrix

/-- The manuscript's ordered free-coordinate basis, equipped with
Euclidean norm on its coefficient vector. -/
def coordinateEuclideanEquiv (n : ℕ) :
    CoordinateSpace n ≃L[ℝ]
      EuclideanSpace ℝ (Fin n ⊕ (Fin n ⊕ Fin n)) :=
  (((coordinateBasis n).equivFun).trans
    (WithLp.linearEquiv 2 ℝ
      ((Fin n ⊕ (Fin n ⊕ Fin n)) → ℝ)).symm).toContinuousLinearEquiv

/-- The manuscript Jacobian matrix acts on the Euclidean coordinates
exactly as the literal Fréchet derivative does in the class chart. -/
theorem coordinateEuclideanEquiv_restrictedJacobian
    {n : ℕ} (ET FT ST : ℝ) (k : Rates n)
    (u v : CoordinateSpace n) :
    coordinateEuclideanEquiv n (restrictedJacobian ET FT ST k u v) =
      Matrix.toEuclideanCLM (n := Fin n ⊕ (Fin n ⊕ Fin n)) (𝕜 := ℝ)
        (restrictedJacobianMatrix ET FT ST k u)
        (coordinateEuclideanEquiv n v) := by
  have hmat := LinearMap.toMatrix_mulVec_repr
    (v₁ := coordinateBasis n) (v₂ := coordinateBasis n)
    (restrictedJacobian ET FT ST k u).toLinearMap v
  change WithLp.toLp 2 (((coordinateBasis n).repr
      (restrictedJacobian ET FT ST k u v) :
        (Fin n ⊕ (Fin n ⊕ Fin n)) → ℝ)) =
    WithLp.toLp 2 ((restrictedJacobianMatrix ET FT ST k u) *ᵥ
      ((coordinateBasis n).repr v :
        (Fin n ⊕ (Fin n ⊕ Fin n)) → ℝ))
  exact congrArg (WithLp.toLp 2) hmat.symm

end
end PhosphorylationStableCapacity
