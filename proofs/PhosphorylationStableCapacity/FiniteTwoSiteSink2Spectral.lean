module
public import proofs.PhosphorylationStableCapacity.FiniteTwoSiteSink2PosDef
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

def twoSiteA2Real : Matrix (Fin 6) (Fin 6) ℝ :=
  manuscriptTwoSiteA2.map (fun q : ℚ => (q : ℝ))

def twoSiteB2Real : Matrix (Fin 6) (Fin 6) ℝ :=
  manuscriptTwoSiteB2.map (fun q : ℚ => (q : ℝ))

def twoSiteP2Real : Matrix (Fin 6) (Fin 6) ℝ :=
  twoSiteB2Realᵀ * twoSiteB2Real

private theorem twoSiteB2Real_upper :
    twoSiteB2Real.IsUpperTriangular := by
  intro i j hij
  fin_cases i <;> fin_cases j <;>
    simp_all [twoSiteB2Real, manuscriptTwoSiteB2]

private theorem twoSiteB2Real_det_ne_zero :
    twoSiteB2Real.det ≠ 0 := by
  rw [Matrix.det_of_isUpperTriangular twoSiteB2Real_upper]
  norm_num [Fin.prod_univ_succ, twoSiteB2Real, manuscriptTwoSiteB2]

theorem twoSiteP2Real_posDef : twoSiteP2Real.PosDef := by
  have hunit : IsUnit twoSiteB2Real := by
    rw [Matrix.isUnit_iff_isUnit_det]
    exact isUnit_iff_ne_zero.mpr twoSiteB2Real_det_ne_zero
  have hinj : Function.Injective twoSiteB2Real.mulVec :=
    Matrix.mulVec_injective_iff_isUnit.mpr hunit
  simpa [twoSiteP2Real, Matrix.conjTranspose_eq_transpose_of_trivial] using
    Matrix.PosDef.conjTranspose_mul_self twoSiteB2Real hinj

theorem twoSiteQ2Real_lyapunov :
    twoSiteA2Real.transpose * twoSiteP2Real +
      twoSiteP2Real * twoSiteA2Real = -twoSiteQ2Real := by
  have h := congrArg
    (fun M : Matrix (Fin 6) (Fin 6) ℚ => M.map (fun q : ℚ => (q : ℝ)))
    manuscriptTwoSiteQ2_eq
  rw [Matrix.map_neg (fun q : ℚ => (q : ℝ)) (by intro q; exact Rat.cast_neg q)] at h
  rw [Matrix.map_add (fun q : ℚ => (q : ℝ))
    (by intro a b; exact Rat.cast_add a b)] at h
  simp only [Matrix.map_mul_ratCast, Matrix.transpose_map] at h
  have hPcast : manuscriptTwoSiteP2.map (fun q : ℚ => (q : ℝ)) =
      twoSiteP2Real := by
    simp [manuscriptTwoSiteP2, twoSiteP2Real, twoSiteB2Real,
      Matrix.map_mul_ratCast, Matrix.transpose_map]
  rw [hPcast] at h
  change twoSiteQ2Real =
    -(twoSiteA2Real.transpose * twoSiteP2Real +
      twoSiteP2Real * twoSiteA2Real) at h
  rw [h]
  simp

theorem twoSiteA2Real_hurwitz :
    ∀ z : ℂ, ((twoSiteA2Real.map (algebraMap ℝ ℂ)).charpoly).eval z = 0 → z.re < 0 := by
  exact hurwitz_of_posDef_lyapunov
    twoSiteA2Real twoSiteP2Real twoSiteQ2Real
    twoSiteP2Real_posDef twoSiteQ2Real_posDef twoSiteQ2Real_lyapunov

end
end PhosphorylationStableCapacity

