module
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.Analysis.Normed.Group.Real

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section

variable {S F : Type*} [AddCommGroup S] [Module ℝ S]
  [AddCommGroup F] [Module ℝ F]

/-- The exact slow Schur operator of a four-block linearization with
invertible fast block. -/
def schurLinear (A : S →ₗ[ℝ] S) (B : F →ₗ[ℝ] S)
    (C : S →ₗ[ℝ] F) (D : F ≃ₗ[ℝ] F) : S →ₗ[ℝ] S :=
  A - B.comp (D.symm.toLinearMap.comp C)

/-- A fast-equilibrium tangent evaluates the Schur operator as the slow
derivative along that same tangent. -/
theorem schurLinear_apply_of_fast_zero
    (A : S →ₗ[ℝ] S) (B : F →ₗ[ℝ] S)
    (C : S →ₗ[ℝ] F) (D : F ≃ₗ[ℝ] F)
    (s : S) (f : F) (hfast : C s + D f = 0) :
    schurLinear A B C D s = A s + B f := by
  have h := congrArg D.symm hfast
  simp only [map_add, LinearEquiv.symm_apply_apply, map_zero] at h
  have hf : D.symm (C s) = -f := eq_neg_of_add_eq_zero_left h
  simp [schurLinear, hf, map_neg, sub_eq_add_neg]

end
end PhosphorylationStableCapacity
