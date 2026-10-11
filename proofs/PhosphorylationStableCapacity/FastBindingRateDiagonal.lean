module
public import proofs.PhosphorylationStableCapacity.FastBindingMatrixPositive

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section
open PhosphorylationSharpness
open Matrix

def fastRateWeights (n : ℕ) (rho sigma : Fin n → ℝ) :
    Fin n ⊕ Fin n → ℝ := Sum.elim rho sigma

/-- The rate matrix acts coordinatewise in the standard complex basis. -/
theorem fastRateMatrix_mulVec {n : ℕ} (rho sigma : Fin n → ℝ)
    (u : Fin n ⊕ Fin n → ℝ) :
    fastRateMatrix n rho sigma *ᵥ u =
      fun a => fastRateWeights n rho sigma a * u a := by
  let v := (fastBasis n).equivFun.symm u
  have hv : (fastBasis n).repr v = u := by
    simpa only [← Module.Basis.equivFun_apply] using
      (fastBasis n).equivFun.apply_symm_apply u
  rw [← hv, fastRateMatrix, LinearMap.toMatrix_mulVec_repr]
  funext a
  cases a with
  | inl i =>
      simp [fastBasis_repr_inl, fastRateWeights, fastRateLinear]
  | inr i =>
      simp [fastBasis_repr_inr, fastRateWeights, fastRateLinear]

theorem fastRateMatrix_eq_diagonal {n : ℕ} (rho sigma : Fin n → ℝ) :
    fastRateMatrix n rho sigma =
      Matrix.diagonal (fastRateWeights n rho sigma) := by
  classical
  ext i j
  have h := congrArg (fun v : Fin n ⊕ Fin n → ℝ => v i)
    (fastRateMatrix_mulVec rho sigma (Pi.single j 1))
  simp only [Matrix.mulVec_single_one] at h
  by_cases hij : i = j
  · subst j
    simpa [Matrix.diagonal_apply] using h
  · have hji : j ≠ i := Ne.symm hij
    simpa [Matrix.diagonal_apply, hij, hji] using h

end
end PhosphorylationStableCapacity
