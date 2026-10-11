module
public import proofs.PhosphorylationStableCapacity.AnalyticSimpleSlowBranch
public import proofs.PhosphorylationStableCapacity.TriangularLinearEquiv
public import proofs.PhosphorylationStableCapacity.MatrixCharpolyAnalytic
public import Mathlib.Analysis.Calculus.Deriv.Polynomial

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section

open Filter Polynomial
open scoped Topology

/-- A polynomial family analytic in the parameter with a simple zero at
coalescence has one analytic zero branch. Its other parameter derivative
may be arbitrary; the triangular inverse only needs the λ pivot. -/
theorem analytic_simple_polynomial_zero_branch
    (P : ℝ → ℝ[X]) (N : ℕ)
    (hdegree : ∀ δ, (P δ).natDegree < N)
    (hcoeff : ∀ k, AnalyticAt ℝ (fun δ => (P δ).coeff k) 0)
    (hzero : (P 0).eval 0 = 0)
    (hpivot : (P 0).derivative.eval 0 ≠ 0) :
    ∃ lam : ℝ → ℝ,
      AnalyticAt ℝ lam 0 ∧ lam 0 = 0 ∧
      ∀ᶠ δ : ℝ in 𝓝 (0 : ℝ), (P δ).eval (lam δ) = 0 := by
  let F : (ℝ × ℝ) → (ℝ × ℝ) :=
    fun q => (q.1, (P q.1).eval q.2)
  have hF : AnalyticAt ℝ F (0, 0) :=
    analyticAt_fst.prod
      (boundedPolynomial_eval_joint_analyticAt P N hdegree hcoeff)
  let L : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ) := fderiv ℝ F (0, 0)
  have hFderiv : HasFDerivAt F L (0, 0) := hF.differentiableAt.hasFDerivAt
  have hfirstderiv : HasFDerivAt (fun q => (F q).1)
      ((ContinuousLinearMap.fst ℝ ℝ ℝ).comp L) (0, 0) :=
    hasFDerivAt_fst.comp _ hFderiv
  have hfirststandard : HasFDerivAt (fun q => (F q).1)
      (ContinuousLinearMap.fst ℝ ℝ ℝ) (0, 0) := by
    simpa only [F] using
      (hasFDerivAt_fst : HasFDerivAt (fun q : ℝ × ℝ => q.1)
        (ContinuousLinearMap.fst ℝ ℝ ℝ) (0, 0))
  have hfirsteq := hfirstderiv.unique hfirststandard
  have hfirst (v : ℝ × ℝ) : (L v).1 = v.1 := by
    have h := congrArg (fun T : (ℝ × ℝ) →L[ℝ] ℝ => T v) hfirsteq
    change (L v).1 = v.1 at h
    exact h
  have hsliceF : HasFDerivAt (fun t : ℝ => F (0, t))
      (L.comp (ContinuousLinearMap.inr ℝ ℝ ℝ)) 0 :=
    hFderiv.comp 0 (hasFDerivAt_prodMk_right (0 : ℝ) (0 : ℝ))
  have hslice : HasFDerivAt (fun t : ℝ => (F (0, t)).2)
      ((ContinuousLinearMap.snd ℝ ℝ ℝ).comp
        (L.comp (ContinuousLinearMap.inr ℝ ℝ ℝ))) 0 :=
    hasFDerivAt_snd.comp 0 hsliceF
  have hpoly : HasFDerivAt (fun t : ℝ => (F (0, t)).2)
      (ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ)
        ((P 0).derivative.eval 0)) 0 := by
    simpa only [F] using (P 0).hasFDerivAt 0
  have hpivoteq : (L (0, 1)).2 = (P 0).derivative.eval 0 := by
    have heq := hslice.unique hpoly
    have h := congrArg (fun T : ℝ →L[ℝ] ℝ => T 1) heq
    change (L (0, 1)).2 = (1 : ℝ) • (P 0).derivative.eval 0 at h
    simpa only [one_smul] using h
  obtain ⟨i, hi⟩ := continuousLinearEquiv_of_triangular_pair
    L hfirst (by simpa only [hpivoteq] using hpivot)
  have hFi : HasFDerivAt F i.toContinuousLinearMap (0, 0) := by
    rw [hi]
    exact hFderiv
  have hFzero : F (0, 0) = (0, 0) := by
    simp only [F, hzero]
  obtain ⟨lam, hlam, hlam0, hroot⟩ :=
    analytic_zero_branch_of_triangular_inverse F i hF hFi hFzero
      (by intro q; rfl)
  refine ⟨lam, hlam, hlam0, ?_⟩
  filter_upwards [hroot] with δ hδ
  have h := congrArg Prod.snd hδ
  simpa only [F] using h

end
end PhosphorylationStableCapacity
