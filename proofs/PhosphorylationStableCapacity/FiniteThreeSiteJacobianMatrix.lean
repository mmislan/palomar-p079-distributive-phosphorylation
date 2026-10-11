module
public import proofs.PhosphorylationStableCapacity.FiniteThreeSiteJacobianAction

@[expose] public section
set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

namespace PhosphorylationStableCapacity

noncomputable section
open PhosphorylationSharpness Module
open scoped Matrix

set_option maxHeartbeats 2000000

/-- Coordinate order `S₁,S₂,S₃,C₀,C₁,C₂,D₀,D₁,D₂`. -/
def threeSiteIndexEquiv :
    (Fin 3 ⊕ (Fin 3 ⊕ Fin 3)) ≃ Fin 9 :=
  { toFun := fun i => match i with
      | .inl j => if j = 0 then 0 else if j = 1 then 1 else 2
      | .inr (.inl j) => if j = 0 then 3 else if j = 1 then 4 else 5
      | .inr (.inr j) => if j = 0 then 6 else if j = 1 then 7 else 8
    invFun := fun i =>
      if i = 0 then .inl 0 else
      if i = 1 then .inl 1 else
      if i = 2 then .inl 2 else
      if i = 3 then .inr (.inl 0) else
      if i = 4 then .inr (.inl 1) else
      if i = 5 then .inr (.inl 2) else
      if i = 6 then .inr (.inr 0) else
      if i = 7 then .inr (.inr 1) else .inr (.inr 2)
    left_inv := by
      intro i
      rcases i with j | j
      · fin_cases j <;> simp
      · rcases j with j | j <;> fin_cases j <;> simp
    right_inv := by
      intro i
      fin_cases i <;> simp }

private def threeSiteBasisVec : Fin 9 → CoordinateSpace 3 :=
  ![(![1,0,0], (![0,0,0], ![0,0,0])),
    (![0,1,0], (![0,0,0], ![0,0,0])),
    (![0,0,1], (![0,0,0], ![0,0,0])),
    (![0,0,0], (![1,0,0], ![0,0,0])),
    (![0,0,0], (![0,1,0], ![0,0,0])),
    (![0,0,0], (![0,0,1], ![0,0,0])),
    (![0,0,0], (![0,0,0], ![1,0,0])),
    (![0,0,0], (![0,0,0], ![0,1,0])),
    (![0,0,0], (![0,0,0], ![0,0,1]))]

private def threeSiteRead : Fin 9 → CoordinateSpace 3 → ℝ :=
  ![fun v => v.1 0, fun v => v.1 1, fun v => v.1 2,
    fun v => v.2.1 0, fun v => v.2.1 1, fun v => v.2.1 2,
    fun v => v.2.2 0, fun v => v.2.2 1, fun v => v.2.2 2]

private theorem threeSiteBasisVec_eq (j : Fin 9) :
    coordinateBasis 3 (threeSiteIndexEquiv.symm j) = threeSiteBasisVec j := by
  fin_cases j <;> ext i <;> fin_cases i <;>
    simp [threeSiteBasisVec, threeSiteIndexEquiv, coordinateBasis]

private theorem threeSiteRead_eq (i : Fin 9) (v : CoordinateSpace 3) :
    (coordinateBasis 3).repr v (threeSiteIndexEquiv.symm i) =
      threeSiteRead i v := by
  fin_cases i <;>
    simp [threeSiteRead, threeSiteIndexEquiv, coordinateBasis]

/-- The exact nine by nine Jacobian in the coordinate order above. -/
def threeSiteExplicitJacobian (ET FT ST : ℝ) (k : Rates 3)
    (u : CoordinateSpace 3) : Matrix (Fin 9) (Fin 9) ℝ :=
  let e := threeSiteFreeE ET u
  let f := threeSiteFreeF FT u
  let s0 := threeSiteFreeS0 ST u
  !![-k.alpha 0 * f - k.a 1 * e, 0, 0,
      k.c 0 + k.a 1 * u.1 0, k.b 1 + k.a 1 * u.1 0, k.a 1 * u.1 0,
      k.beta 0 + k.alpha 0 * u.1 0, k.gamma 1 + k.alpha 0 * u.1 0,
      k.alpha 0 * u.1 0;
    0, -k.alpha 1 * f - k.a 2 * e, 0,
      k.a 2 * u.1 1, k.c 1 + k.a 2 * u.1 1,
      k.b 2 + k.a 2 * u.1 1,
      k.alpha 1 * u.1 1, k.beta 1 + k.alpha 1 * u.1 1,
      k.gamma 2 + k.alpha 1 * u.1 1;
    0, 0, -k.alpha 2 * f, 0, 0, k.c 2,
      k.alpha 2 * u.1 2, k.alpha 2 * u.1 2,
      k.beta 2 + k.alpha 2 * u.1 2;
    -k.a 0 * e, -k.a 0 * e, -k.a 0 * e,
      -k.a 0 * (s0 + e) - k.b 0 - k.c 0,
      -k.a 0 * (s0 + e), -k.a 0 * (s0 + e),
      -k.a 0 * e, -k.a 0 * e, -k.a 0 * e;
    k.a 1 * e, 0, 0,
      -k.a 1 * u.1 0, -k.a 1 * u.1 0 - k.b 1 - k.c 1,
      -k.a 1 * u.1 0, 0, 0, 0;
    0, k.a 2 * e, 0,
      -k.a 2 * u.1 1, -k.a 2 * u.1 1,
      -k.a 2 * u.1 1 - k.b 2 - k.c 2, 0, 0, 0;
    k.alpha 0 * f, 0, 0, 0, 0, 0,
      -k.alpha 0 * u.1 0 - k.beta 0 - k.gamma 0,
      -k.alpha 0 * u.1 0, -k.alpha 0 * u.1 0;
    0, k.alpha 1 * f, 0, 0, 0, 0,
      -k.alpha 1 * u.1 1,
      -k.alpha 1 * u.1 1 - k.beta 1 - k.gamma 1,
      -k.alpha 1 * u.1 1;
    0, 0, k.alpha 2 * f, 0, 0, 0,
      -k.alpha 2 * u.1 2, -k.alpha 2 * u.1 2,
      -k.alpha 2 * u.1 2 - k.beta 2 - k.gamma 2]

theorem threeSiteMatrixFin_eq_explicit (ET FT ST : ℝ) (k : Rates 3)
    (u : CoordinateSpace 3) :
    Matrix.reindex threeSiteIndexEquiv threeSiteIndexEquiv
        (restrictedJacobianMatrix ET FT ST k u) =
      threeSiteExplicitJacobian ET FT ST k u := by
  rw [restrictedJacobianMatrix, restrictedJacobian_threeSite]
  ext i j
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply,
    LinearMap.toMatrix_apply]
  rw [threeSiteRead_eq, threeSiteBasisVec_eq]
  fin_cases i <;> fin_cases j <;>
    simp [threeSiteRead, threeSiteBasisVec, threeSiteJacobianCLM,
      threeSiteRowS1, threeSiteRowS2, threeSiteRowS3,
      threeSiteRowC0, threeSiteRowC1, threeSiteRowC2,
      threeSiteRowD0, threeSiteRowD1, threeSiteRowD2,
      threeSiteS0Linear, threeSiteELinear, threeSiteFLinear,
      threeSitePS, threeSitePC, threeSitePD,
      threeSiteExplicitJacobian] <;> ring

end
end PhosphorylationStableCapacity
