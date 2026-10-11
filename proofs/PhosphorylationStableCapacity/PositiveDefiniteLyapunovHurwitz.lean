module
public import Mathlib.LinearAlgebra.Eigenspace.Charpoly
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.Basic.Complex.BigOperators
public import Mathlib.LinearAlgebra.Complex.Module
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Push

@[expose] public section
set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

namespace PhosphorylationStableCapacity

noncomputable section
open Matrix
open scoped BigOperators

private theorem lyapunov_quadratic_identity {ι : Type*} [Fintype ι]
    (A P : Matrix ι ι ℝ) (hP : P.IsSymm) (x : ι → ℝ) :
    x ⬝ᵥ ((A.transpose * P + P * A) *ᵥ x) =
      2 * (x ⬝ᵥ (P *ᵥ (A *ᵥ x))) := by
  rw [Matrix.add_mulVec, dotProduct_add,
    ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  rw [Matrix.dotProduct_transpose_mulVec]
  have hsym : (P *ᵥ x) ⬝ᵥ (A *ᵥ x) = x ⬝ᵥ (P *ᵥ (A *ᵥ x)) := by
    rw [dotProduct_comm, ← Matrix.dotProduct_transpose_mulVec, hP]
  rw [hsym]
  ring

/-- A positive definite Lyapunov pair gives a spectral certificate for an
arbitrary real matrix, including nonsymmetric class Jacobians. -/
theorem hurwitz_of_posDef_lyapunov {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A P Q : Matrix ι ι ℝ) (hP : P.PosDef) (hQ : Q.PosDef)
    (hEq : A.transpose * P + P * A = -Q) :
    ∀ z : ℂ, ((A.map (algebraMap ℝ ℂ)).charpoly).eval z = 0 → z.re < 0 := by
  intro z hz
  let AC : Matrix ι ι ℂ := A.map (algebraMap ℝ ℂ)
  have heig : Module.End.HasEigenvalue (Matrix.toLin' AC) z := by
    rw [Module.End.hasEigenvalue_iff_isRoot_charpoly, Matrix.charpoly_toLin']
    exact hz
  obtain ⟨v, hv⟩ := heig.exists_hasEigenvector
  have hev : AC *ᵥ v = z • v := hv.apply_eq_smul
  let x : ι → ℝ := fun i => (v i).re
  let y : ι → ℝ := fun i => (v i).im
  have hxy : x ≠ 0 ∨ y ≠ 0 := by
    by_contra h
    push Not at h
    apply hv.2
    ext i
    apply Complex.ext
    · exact congr_fun h.1 i
    · exact congr_fun h.2 i
  have hAx : A *ᵥ x = z.re • x - z.im • y := by
    ext i
    have hi := congrArg Complex.re (congr_fun hev i)
    simpa [AC, x, y, Matrix.mulVec, dotProduct, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im, add_comm] using hi
  have hAy : A *ᵥ y = z.im • x + z.re • y := by
    ext i
    have hi := congrArg Complex.im (congr_fun hev i)
    simpa [AC, x, y, Matrix.mulVec, dotProduct, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, add_comm] using hi
  have hquad (R : Matrix ι ι ℝ) (hR : R.PosDef) :
      0 < x ⬝ᵥ (R *ᵥ x) + y ⬝ᵥ (R *ᵥ y) := by
    have hnonneg (u : ι → ℝ) : 0 ≤ u ⬝ᵥ (R *ᵥ u) := by
      by_cases hu : u = 0
      · simp [hu]
      · simpa only [star_trivial] using (hR.dotProduct_mulVec_pos hu).le
    rcases hxy with hx | hy
    · exact add_pos_of_pos_of_nonneg
        (by simpa only [star_trivial] using hR.dotProduct_mulVec_pos hx) (hnonneg y)
    · exact add_pos_of_nonneg_of_pos (hnonneg x)
        (by simpa only [star_trivial] using hR.dotProduct_mulVec_pos hy)
  have hsym : y ⬝ᵥ (P *ᵥ x) = x ⬝ᵥ (P *ᵥ y) := by
    rw [← Matrix.dotProduct_transpose_mulVec, hP.isHermitian.isSymm]
  have hsum :
      -(x ⬝ᵥ (Q *ᵥ x) + y ⬝ᵥ (Q *ᵥ y)) =
        2 * z.re * (x ⬝ᵥ (P *ᵥ x) + y ⬝ᵥ (P *ᵥ y)) := by
    have hx := lyapunov_quadratic_identity A P hP.isHermitian.isSymm x
    have hy := lyapunov_quadratic_identity A P hP.isHermitian.isSymm y
    rw [hEq, Matrix.neg_mulVec, dotProduct_neg, hAx,
      Matrix.mulVec_sub, Matrix.mulVec_smul, Matrix.mulVec_smul,
      dotProduct_sub, dotProduct_smul, dotProduct_smul] at hx
    rw [hEq, Matrix.neg_mulVec, dotProduct_neg, hAy,
      Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul,
      dotProduct_add, dotProduct_smul, dotProduct_smul, hsym] at hy
    dsimp only [smul_eq_mul] at hx hy
    nlinarith
  have hp := hquad P hP
  have hq := hquad Q hQ
  nlinarith

end
end PhosphorylationStableCapacity
