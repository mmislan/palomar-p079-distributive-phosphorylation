module
public import proofs.PhosphorylationStableCapacity.AnalyticJointRestrictedField
public import Mathlib.Analysis.Calculus.FDeriv.Analytic

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section

open PhosphorylationSharpness Matrix

/-- The class Jacobian is the coordinate-direction restriction of the total
Fréchet derivative of the joint mass-action field. -/
theorem restrictedJacobian_eq_joint_fderiv_comp {n : ℕ}
    (ET FT ST : ℝ) (v : RateVector n) (u : CoordinateSpace n) :
    restrictedJacobian ET FT ST (ratesFromVector v) u =
      (fderiv ℝ (jointRestrictedField ET FT ST) (v, u)).comp
        (ContinuousLinearMap.inr ℝ (RateVector n) (CoordinateSpace n)) := by
  have hg : DifferentiableAt ℝ (jointRestrictedField ET FT ST) (v, u) :=
    (analyticAt_jointRestrictedField ET FT ST (v, u)).differentiableAt
  have hinput : DifferentiableAt ℝ (fun y : CoordinateSpace n => (v, y)) u :=
    (hasFDerivAt_prodMk_right v u).differentiableAt
  have hchain := fderiv_comp u hg hinput
  simpa only [restrictedJacobian, jointRestrictedField,
    Function.comp_def, (hasFDerivAt_prodMk_right v u).fderiv] using hchain

/-- Each literal matrix entry is analytic in an analytic rate/state path. -/
theorem restrictedJacobianMatrix_parameter_analyticAt
    (n : ℕ) (ET FT ST : ℝ)
    (k : ℝ → Rates n) (u : ℝ → CoordinateSpace n)
    (hk : AnalyticAt ℝ (fun δ => rateVector (k δ)) 0)
    (hu : AnalyticAt ℝ u 0) :
    ∀ i j, AnalyticAt ℝ (fun δ =>
      restrictedJacobianMatrix ET FT ST (k δ) (u δ) i j) 0 := by
  let g : RateVector n × CoordinateSpace n → CoordinateSpace n :=
    jointRestrictedField ET FT ST
  have hinput : AnalyticAt ℝ
      (fun δ => (rateVector (k δ), u δ)) 0 := hk.prod hu
  have hg : AnalyticAt ℝ (fderiv ℝ g)
      (rateVector (k 0), u 0) :=
    (analyticAt_jointRestrictedField ET FT ST _).fderiv
  have hderiv : AnalyticAt ℝ (fun δ =>
      fderiv ℝ g (rateVector (k δ), u δ)) 0 :=
    hg.comp (f := fun δ : ℝ => (rateVector (k δ), u δ)) hinput
  intro i j
  let direction : RateVector n × CoordinateSpace n :=
    ContinuousLinearMap.inr ℝ (RateVector n) (CoordinateSpace n)
      (coordinateBasis n j)
  have heval : AnalyticAt ℝ (fun δ =>
      (fderiv ℝ g (rateVector (k δ), u δ)) direction) 0 :=
    ((ContinuousLinearMap.apply ℝ (CoordinateSpace n)
      direction).analyticAt _).comp
        (f := fun δ : ℝ => fderiv ℝ g (rateVector (k δ), u δ)) hderiv
  let hlin : CoordinateSpace n →ₗ[ℝ] ℝ :=
    (Finsupp.lapply i :
      ((Fin n ⊕ Fin n ⊕ Fin n) →₀ ℝ) →ₗ[ℝ] ℝ).comp
        (coordinateBasis n).repr.toLinearMap
  have hrepr : AnalyticAt ℝ
      (fun x : CoordinateSpace n => (coordinateBasis n).repr x i)
      ((fderiv ℝ g (rateVector (k 0), u 0)) direction) := by
    have hident : (fun x : CoordinateSpace n =>
        (coordinateBasis n).repr x i) = hlin := by
      funext x
      simp [hlin]
    rw [hident]
    exact hlin.toContinuousLinearMap.analyticAt _
  have hentry := hrepr.comp
    (f := fun δ : ℝ => (fderiv ℝ g (rateVector (k δ), u δ)) direction) heval
  have heq (δ : ℝ) :
      restrictedJacobian ET FT ST (k δ) (u δ) =
        (fderiv ℝ g (rateVector (k δ), u δ)).comp
          (ContinuousLinearMap.inr ℝ (RateVector n) (CoordinateSpace n)) := by
    rw [← ratesFromVector_rateVector (k δ)]
    exact restrictedJacobian_eq_joint_fderiv_comp ET FT ST _ _
  simpa only [restrictedJacobianMatrix, LinearMap.toMatrix_apply,
    ContinuousLinearMap.coe_coe, Function.comp_def, heq,
    direction, ContinuousLinearMap.comp_apply] using hentry

end
end PhosphorylationStableCapacity
