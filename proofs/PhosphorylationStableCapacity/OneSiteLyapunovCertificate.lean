module
public import proofs.PhosphorylationStableCapacity.HurwitzSpectralGap
public import proofs.PhosphorylationStableCapacity.BaseCase
public import Mathlib.LinearAlgebra.Matrix.PosDef

@[expose] public section
set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

namespace PhosphorylationStableCapacity

open scoped Matrix

noncomputable section

/-- The literal unit-rate one-site Jacobian in the chart order
`S₁,C₀,D₀`, as calculated in `BaseCase.lean`. -/
def oneSiteA : Matrix (Fin 3) (Fin 3) ℝ :=
  !![-1, 1, 2; -1, -4, -1; 1, 0, -3]

def oneSiteIndexEquiv :
    (Fin 1 ⊕ (Fin 1 ⊕ Fin 1)) ≃ Fin 3 :=
  oneIndexEquiv

/-- The pilot matrix is exactly the literal restricted Jacobian after
the standard coordinate reindexing. -/
theorem oneSiteA_eq_literal_jacobian :
    Matrix.reindex oneSiteIndexEquiv oneSiteIndexEquiv
      (restrictedJacobianMatrix (3/2) (3/2) 3 oneRates oneCoord) =
        oneSiteA := by
  simpa [oneSiteA, oneSiteIndexEquiv, oneMatrixFin] using oneMatrixFin_eq

/-- An exact rational Lyapunov matrix found by the bounded symbolic
one-site pilot. -/
def oneSiteP : Matrix (Fin 3) (Fin 3) ℝ :=
  !![13/16, 5/34, 125/272;
     5/34, 11/68, 23/272;
     125/272, 23/272, 121/272]

theorem oneSite_lyapunov_identity :
    oneSiteAᵀ * oneSiteP + oneSiteP * oneSiteA =
      -(1 : Matrix (Fin 3) (Fin 3) ℝ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [oneSiteA, oneSiteP, Matrix.mul_apply,
      Fin.sum_univ_succ, Matrix.add_apply, Matrix.neg_apply,
      Matrix.one_apply, Matrix.transpose_apply]

private theorem oneSiteP_quadratic (x : Fin 3 → ℝ) :
    star x ⬝ᵥ (oneSiteP *ᵥ x) =
      (13/16 : ℝ) * (x 0 + (40/221) * x 1 + (125/221) * x 2)^2 +
      (2031/15028 : ℝ) * (x 1 + (83/8124) * x 2)^2 +
      (24035/129984 : ℝ) * (x 2)^2 := by
  simp [oneSiteP, dotProduct, Matrix.mulVec, Fin.sum_univ_succ]
  ring

theorem oneSiteP_posDef : oneSiteP.PosDef := by
  apply Matrix.PosDef.of_dotProduct_mulVec_pos
  · ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [oneSiteP, Matrix.conjTranspose_apply, Matrix.transpose_apply]
  · intro x hx
    rw [oneSiteP_quadratic]
    by_cases h2 : x 2 = 0
    · by_cases h1 : x 1 = 0
      · have h0 : x 0 ≠ 0 := by
          intro h0
          apply hx
          funext i
          fin_cases i <;> simp [h0, h1, h2]
        have hs0 := sq_pos_of_ne_zero h0
        simp [h1, h2]
        nlinarith
      · have hs0 := sq_nonneg (x 0 + (40/221) * x 1)
        have hs1 := sq_pos_of_ne_zero h1
        simp [h2]
        nlinarith
    · have hs0 := sq_nonneg
        (x 0 + (40/221) * x 1 + (125/221) * x 2)
      have hs1 := sq_nonneg (x 1 + (83/8124) * x 2)
      have hs2 := sq_pos_of_ne_zero h2
      nlinarith

end
end PhosphorylationStableCapacity
