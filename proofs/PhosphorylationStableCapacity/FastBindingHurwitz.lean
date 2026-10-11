module
public import proofs.PhosphorylationStableCapacity.FastBindingSymmetricRate
public import proofs.PhosphorylationStableCapacity.NegativeDefiniteHurwitz

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section
open PhosphorylationSharpness
open Matrix

/-- The literal fast matrix has the characteristic polynomial of a symmetric
negative-definite matrix. -/
theorem fastBindingMatrix_charpoly_eq_neg_symmetric {n : ℕ}
    (x : State n) (rho sigma : Fin n → ℝ)
    (hρ : ∀ i, 0 < rho i) (hσ : ∀ i, 0 < sigma i) :
    (fastBindingMatrix n x rho sigma).charpoly =
      (-(fastSymmetricBindingMatrix n x rho sigma)).charpoly := by
  let T := fastSqrtRateMatrix n rho sigma
  let H := fastAffinityMatrix n x
  have hT : Tᴴ = T := fastSqrtRateMatrix_isHermitian rho sigma
  have hR : fastRateMatrix n rho sigma = T * T :=
    (fastSqrtRateMatrix_sq rho sigma hρ hσ).symm
  calc
    (fastBindingMatrix n x rho sigma).charpoly =
        (-(fastRateMatrix n rho sigma * H)).charpoly := by
          rw [fastBindingMatrix_factorization]
    _ = (T * (-(T * H))).charpoly := by rw [hR]; simp [mul_assoc]
    _ = ((-(T * H)) * T).charpoly := Matrix.charpoly_mul_comm _ _
    _ = (-(fastSymmetricBindingMatrix n x rho sigma)).charpoly := by
      have hm : (-(T * H)) * T =
          -(fastSymmetricBindingMatrix n x rho sigma) := by
        change (-(T * H)) * T = -(Tᴴ * H * T)
        rw [hT]
        simp [mul_assoc]
      exact congrArg Matrix.charpoly hm

/-- The exact fast-fast Jacobian matrix is Hurwitz at every positive state. -/
theorem fastBindingMatrix_hurwitz {n : ℕ} (x : State n)
    (hx : x.Positive) (rho sigma : Fin n → ℝ)
    (hρ : ∀ i, 0 < rho i) (hσ : ∀ i, 0 < sigma i) :
    IsHurwitz (fastBindingMatrix n x rho sigma) := by
  have hS := fastSymmetricBindingMatrix_posDef x hx rho sigma hρ hσ
  have hchar := fastBindingMatrix_charpoly_eq_neg_symmetric x rho sigma hρ hσ
  have hmap :
      ((fastBindingMatrix n x rho sigma).map (algebraMap ℝ ℂ)).charpoly =
      ((-(fastSymmetricBindingMatrix n x rho sigma)).map
        (algebraMap ℝ ℂ)).charpoly := by
    simpa only [Matrix.charpoly_map] using
      congrArg (fun p : Polynomial ℝ => p.map (algebraMap ℝ ℂ)) hchar
  intro z hz
  exact (isHurwitz_neg_of_posDef _ hS) z (by simpa only [hmap] using hz)

end
end PhosphorylationStableCapacity
