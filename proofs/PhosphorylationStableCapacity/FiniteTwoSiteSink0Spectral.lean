module
public import proofs.PhosphorylationStableCapacity.FiniteTwoSitePosDefCertificate
public import proofs.PhosphorylationStableCapacity.PositiveDefiniteLyapunovHurwitz
public import Mathlib.LinearAlgebra.Matrix.Integer
public import Mathlib.LinearAlgebra.Matrix.Block
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.FinCases

@[expose] public section
set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

namespace PhosphorylationStableCapacity

noncomputable section
open scoped Matrix

set_option maxHeartbeats 2000000

def twoSiteA0Real : Matrix (Fin 6) (Fin 6) ℝ :=
  manuscriptTwoSiteA0.map (fun q : ℚ => (q : ℝ))

def twoSiteB0Real : Matrix (Fin 6) (Fin 6) ℝ :=
  manuscriptTwoSiteB0.map (fun q : ℚ => (q : ℝ))

def twoSiteP0Real : Matrix (Fin 6) (Fin 6) ℝ :=
  twoSiteB0Realᵀ * twoSiteB0Real

private theorem twoSiteB0Real_upper :
    twoSiteB0Real.IsUpperTriangular := by
  intro i j hij
  fin_cases i <;> fin_cases j <;>
    simp_all [twoSiteB0Real, manuscriptTwoSiteB0]

private theorem twoSiteB0Real_det_ne_zero :
    twoSiteB0Real.det ≠ 0 := by
  rw [Matrix.det_of_isUpperTriangular twoSiteB0Real_upper]
  norm_num [Fin.prod_univ_succ, twoSiteB0Real, manuscriptTwoSiteB0]

theorem twoSiteP0Real_posDef : twoSiteP0Real.PosDef := by
  have hunit : IsUnit twoSiteB0Real := by
    rw [Matrix.isUnit_iff_isUnit_det]
    exact isUnit_iff_ne_zero.mpr twoSiteB0Real_det_ne_zero
  have hinj : Function.Injective twoSiteB0Real.mulVec :=
    Matrix.mulVec_injective_iff_isUnit.mpr hunit
  simpa [twoSiteP0Real, Matrix.conjTranspose_eq_transpose_of_trivial] using
    Matrix.PosDef.conjTranspose_mul_self twoSiteB0Real hinj

theorem twoSiteQ0Real_lyapunov :
    twoSiteA0Real.transpose * twoSiteP0Real +
      twoSiteP0Real * twoSiteA0Real = -twoSiteQ0Real := by
  have h := congrArg
    (fun M : Matrix (Fin 6) (Fin 6) ℚ => M.map (fun q : ℚ => (q : ℝ)))
    manuscriptTwoSiteQ0_eq
  rw [Matrix.map_neg (fun q : ℚ => (q : ℝ)) (by intro q; exact Rat.cast_neg q)] at h
  rw [Matrix.map_add (fun q : ℚ => (q : ℝ))
    (by intro a b; exact Rat.cast_add a b)] at h
  simp only [Matrix.map_mul_ratCast, Matrix.transpose_map] at h
  have hPcast : manuscriptTwoSiteP0.map (fun q : ℚ => (q : ℝ)) =
      twoSiteP0Real := by
    simp [manuscriptTwoSiteP0, twoSiteP0Real, twoSiteB0Real,
      Matrix.map_mul_ratCast, Matrix.transpose_map]
  rw [hPcast] at h
  change twoSiteQ0Real =
    -(twoSiteA0Real.transpose * twoSiteP0Real +
      twoSiteP0Real * twoSiteA0Real) at h
  rw [h]
  simp

theorem twoSiteA0Real_hurwitz :
    ∀ z : ℂ, ((twoSiteA0Real.map (algebraMap ℝ ℂ)).charpoly).eval z = 0 → z.re < 0 := by
  exact hurwitz_of_posDef_lyapunov
    twoSiteA0Real twoSiteP0Real twoSiteQ0Real
    twoSiteP0Real_posDef twoSiteQ0Real_posDef twoSiteQ0Real_lyapunov

end
end PhosphorylationStableCapacity
