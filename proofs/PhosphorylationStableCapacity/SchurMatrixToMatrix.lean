module
public import proofs.PhosphorylationStableCapacity.FastSlowSchurAlgebra
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Charpoly.ToMatrix

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section

open Matrix Module

/-- The matrix of the inverse linear equivalence is the nonsingular
inverse of the equivalence's matrix in the same basis. -/
theorem linearEquiv_symm_toMatrix_eq_inv
    {F : Type*} [AddCommGroup F] [Module ℝ F]
    {f : Type*} [Fintype f] [DecidableEq f]
    (bF : Basis f ℝ F) (D : F ≃ₗ[ℝ] F) :
    LinearMap.toMatrix bF bF D.symm.toLinearMap =
      (LinearMap.toMatrix bF bF D.toLinearMap)⁻¹ := by
  have hcomp : D.toLinearMap.comp D.symm.toLinearMap = LinearMap.id := by
    apply LinearMap.ext
    intro v
    simp
  have hprod : LinearMap.toMatrix bF bF D.toLinearMap *
      LinearMap.toMatrix bF bF D.symm.toLinearMap = 1 := by
    rw [← LinearMap.toMatrix_comp, hcomp, LinearMap.toMatrix_id]
  exact (Matrix.inv_eq_right_inv hprod).symm

/-- Matrix representation commutes with the exact slow Schur operator. -/
theorem schurLinear_toMatrix
    {S F : Type*} [AddCommGroup S] [Module ℝ S]
    [AddCommGroup F] [Module ℝ F]
    {s f : Type*} [Fintype s] [Fintype f]
    [DecidableEq s] [DecidableEq f]
    (bS : Basis s ℝ S) (bF : Basis f ℝ F)
    (A : S →ₗ[ℝ] S) (B : F →ₗ[ℝ] S)
    (C : S →ₗ[ℝ] F) (D : F ≃ₗ[ℝ] F) :
    LinearMap.toMatrix bS bS (schurLinear A B C D) =
      LinearMap.toMatrix bS bS A -
        LinearMap.toMatrix bF bS B *
          (LinearMap.toMatrix bF bF D.toLinearMap)⁻¹ *
            LinearMap.toMatrix bS bF C := by
  unfold schurLinear
  simp only [map_sub]
  rw [LinearMap.toMatrix_comp bS bF bS B
      (D.symm.toLinearMap.comp C),
    LinearMap.toMatrix_comp bS bF bF D.symm.toLinearMap C,
    linearEquiv_symm_toMatrix_eq_inv]
  rw [Matrix.mul_assoc]

/-- The characteristic polynomial of a Schur endomorphism equals that
of the explicit matrix Schur complement. -/
theorem schurLinear_charpoly_eq_matrix
    {S F : Type*} [AddCommGroup S] [Module ℝ S]
    [FiniteDimensional ℝ S]
    [AddCommGroup F] [Module ℝ F]
    {s f : Type*} [Fintype s] [Fintype f]
    [DecidableEq s] [DecidableEq f]
    (bS : Basis s ℝ S) (bF : Basis f ℝ F)
    (A : S →ₗ[ℝ] S) (B : F →ₗ[ℝ] S)
    (C : S →ₗ[ℝ] F) (D : F ≃ₗ[ℝ] F) :
    (schurLinear A B C D).charpoly =
      (LinearMap.toMatrix bS bS A -
        LinearMap.toMatrix bF bS B *
          (LinearMap.toMatrix bF bF D.toLinearMap)⁻¹ *
            LinearMap.toMatrix bS bF C).charpoly := by
  rw [← LinearMap.charpoly_toMatrix (schurLinear A B C D) bS,
    schurLinear_toMatrix bS bF A B C D]

end
end PhosphorylationStableCapacity
