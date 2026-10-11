module
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Analytic

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section

/-- The analytic inverse-function theorem for a map between Banach spaces.
The one-dimensional version is in mathlib; this form will be used for the
triangular parameter/eigenvalue map `(δ, λ) ↦ (δ, P δ λ)`. -/
theorem analyticAt_localInverse_general
    {𝕜 E F : Type*} [NontriviallyNormedField 𝕜] [CharZero 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F] [CompleteSpace F]
    {f : E → F} {x : E} (i : E ≃L[𝕜] F)
    (hf : AnalyticAt 𝕜 f x)
    (hfd : HasStrictFDerivAt f i.toContinuousLinearMap x) :
    AnalyticAt 𝕜
      ((hfd.toOpenPartialHomeomorph f).symm)
      (f x) := by
  let R : OpenPartialHomeomorph E F := hfd.toOpenPartialHomeomorph f
  obtain ⟨p, hp⟩ := hf
  have hp₁ : p 1 =
      (continuousMultilinearCurryFin1 𝕜 E F).symm i := by
    apply (continuousMultilinearCurryFin1 𝕜 E F).injective
    calc
      (continuousMultilinearCurryFin1 𝕜 E F) (p 1) =
          i.toContinuousLinearMap :=
        hp.hasFDerivAt.unique hfd.hasFDerivAt
      _ = (continuousMultilinearCurryFin1 𝕜 E F)
          ((continuousMultilinearCurryFin1 𝕜 E F).symm i) := by
        simp
  change AnalyticAt 𝕜 R.symm (f x)
  exact (R.hasFPowerSeriesAt_symm
    hfd.mem_toOpenPartialHomeomorph_source hp hp₁).analyticAt

end
end PhosphorylationStableCapacity
