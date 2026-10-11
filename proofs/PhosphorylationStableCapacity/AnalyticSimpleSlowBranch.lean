module
public import proofs.PhosphorylationStableCapacity.AnalyticLocalInverseGeneral

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section

open Filter
open scoped Topology

/-- An analytic, locally invertible triangular equation has an analytic
zero branch. The concrete characteristic polynomial will be supplied as
the second component of `F`. -/
theorem analytic_zero_branch_of_triangular_inverse
    (F : (ℝ × ℝ) → (ℝ × ℝ))
    (i : (ℝ × ℝ) ≃L[ℝ] (ℝ × ℝ))
    (hF : AnalyticAt ℝ F (0, 0))
    (hderiv : HasFDerivAt F i.toContinuousLinearMap (0, 0))
    (hFzero : F (0, 0) = (0, 0))
    (hfirst : ∀ x : ℝ × ℝ, (F x).1 = x.1) :
    ∃ lam : ℝ → ℝ,
      AnalyticAt ℝ lam 0 ∧ lam 0 = 0 ∧
      ∀ᶠ δ : ℝ in 𝓝 (0 : ℝ), F (δ, lam δ) = (δ, 0) := by
  have hfd : HasStrictFDerivAt F i.toContinuousLinearMap (0, 0) := by
    simpa only [hderiv.fderiv] using hF.hasStrictFDerivAt
  let R : OpenPartialHomeomorph (ℝ × ℝ) (ℝ × ℝ) :=
    hfd.toOpenPartialHomeomorph F
  let v : ℝ → ℝ × ℝ := fun δ => R.symm (δ, 0)
  let lam : ℝ → ℝ := fun δ => (v δ).2
  have hR : AnalyticAt ℝ R.symm (0, 0) := by
    simpa only [hFzero] using
      analyticAt_localInverse_general i hF hfd
  have hv : AnalyticAt ℝ v 0 := by
    have hinner : AnalyticAt ℝ
        (fun δ : ℝ => (δ, (0 : ℝ))) 0 :=
      analyticAt_id.prod analyticAt_const
    have hcomp : AnalyticAt ℝ
        (R.symm ∘ fun δ : ℝ => (δ, (0 : ℝ))) 0 :=
      hR.comp (f := fun δ : ℝ => (δ, (0 : ℝ))) hinner
    simpa only [v, Function.comp_def] using hcomp
  have hlam : AnalyticAt ℝ lam 0 := by
    exact analyticAt_snd.comp hv
  have hvzero : v 0 = (0, 0) := by
    change R.symm (0, 0) = (0, 0)
    simpa only [HasStrictFDerivAt.localInverse_def, hFzero]
      using hfd.localInverse_apply_image
  have hright : ∀ᶠ δ : ℝ in 𝓝 (0 : ℝ),
      F (v δ) = (δ, 0) := by
    have h : ∀ᶠ z : ℝ × ℝ in 𝓝 (0, 0),
        F (R.symm z) = z := by
      simpa only [HasStrictFDerivAt.localInverse_def, hFzero] using
        hfd.eventually_right_inverse
    have hcont : ContinuousAt
        (fun δ : ℝ => (δ, (0 : ℝ))) 0 := by fun_prop
    exact hcont.tendsto.eventually h
  refine ⟨lam, hlam, by simp [lam, hvzero], ?_⟩
  filter_upwards [hright] with δ hδ
  have hvfirst : (v δ).1 = δ := by
    have h := congrArg Prod.fst hδ
    simpa only [hfirst] using h
  have hvpair : (δ, lam δ) = v δ := by
    apply Prod.ext
    · exact hvfirst.symm
    · rfl
  rw [hvpair]
  exact hδ

end
end PhosphorylationStableCapacity
