module
public import proofs.PhosphorylationStableCapacity.LoadedFieldDifferentiability

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section

/-- The exact loaded class derivative has unchanged slow rows and fast rows
scaled by `epsilon⁻¹`, at every class point. -/
theorem loadedFderiv_relax_blocks {n : ℕ} (ET FT ST : ℝ)
    (k : PhosphorylationSharpness.Rates n) (u v : CoordinateSpace n)
    {ε : ℝ} (hε : ε ≠ 0) :
    fderiv ℝ (loadedRestrictedField ET FT ST (relaxRates k ε)) u v =
      ((fderiv ℝ (loadedRestrictedField ET FT ST k) u v).1,
        ε⁻¹ • (fderiv ℝ (loadedRestrictedField ET FT ST k) u v).2.1,
        ε⁻¹ • (fderiv ℝ (loadedRestrictedField ET FT ST k) u v).2.2) := by
  let f := loadedRestrictedField ET FT ST k
  let g := loadedRestrictedField ET FT ST (relaxRates k ε)
  have hf : DifferentiableAt ℝ f u :=
    (differentiable_loadedRestrictedField ET FT ST k).differentiableAt
  have hg : DifferentiableAt ℝ g u :=
    (differentiable_loadedRestrictedField ET FT ST (relaxRates k ε)).differentiableAt
  have hslowf :
      (fderiv ℝ (fun z => (f z).1) u) v = (fderiv ℝ f u v).1 := by
    have h := congrArg (fun L : CoordinateSpace n →L[ℝ] (Fin n → ℝ) => L v)
      hf.hasFDerivAt.fst.fderiv
    exact h
  have hslowg :
      (fderiv ℝ (fun z => (g z).1) u) v = (fderiv ℝ g u v).1 := by
    have h := congrArg (fun L : CoordinateSpace n →L[ℝ] (Fin n → ℝ) => L v)
      hg.hasFDerivAt.fst.fderiv
    exact h
  have hCf :
      (fderiv ℝ (fun z => (f z).2.1) u) v = (fderiv ℝ f u v).2.1 := by
    have h := congrArg (fun L : CoordinateSpace n →L[ℝ] (Fin n → ℝ) => L v)
      hf.hasFDerivAt.snd.fst.fderiv
    exact h
  have hCg :
      (fderiv ℝ (fun z => (g z).2.1) u) v = (fderiv ℝ g u v).2.1 := by
    have h := congrArg (fun L : CoordinateSpace n →L[ℝ] (Fin n → ℝ) => L v)
      hg.hasFDerivAt.snd.fst.fderiv
    exact h
  have hDf :
      (fderiv ℝ (fun z => (f z).2.2) u) v = (fderiv ℝ f u v).2.2 := by
    have h := congrArg (fun L : CoordinateSpace n →L[ℝ] (Fin n → ℝ) => L v)
      hf.hasFDerivAt.snd.snd.fderiv
    exact h
  have hDg :
      (fderiv ℝ (fun z => (g z).2.2) u) v = (fderiv ℝ g u v).2.2 := by
    have h := congrArg (fun L : CoordinateSpace n →L[ℝ] (Fin n → ℝ) => L v)
      hg.hasFDerivAt.snd.snd.fderiv
    exact h
  have hs := congrArg (fun L : CoordinateSpace n →L[ℝ] (Fin n → ℝ) => L v)
    (loadedSlowFderiv_relax ET FT ST k u ε)
  have hc := congrArg (fun L : CoordinateSpace n →L[ℝ] (Fin n → ℝ) => L v)
    (loadedCFderiv_relax ET FT ST k u hε)
  have hd := congrArg (fun L : CoordinateSpace n →L[ℝ] (Fin n → ℝ) => L v)
    (loadedDFderiv_relax ET FT ST k u hε)
  apply Prod.ext
  · exact hslowg.symm.trans (hs.trans hslowf)
  · apply Prod.ext
    · calc
        (fderiv ℝ g u v).2.1 =
            (fderiv ℝ (fun z => (g z).2.1) u) v := hCg.symm
        _ = ε⁻¹ • (fderiv ℝ (fun z => (f z).2.1) u) v := by
          simpa only [smul_apply] using hc
        _ = ε⁻¹ • (fderiv ℝ f u v).2.1 :=
          congrArg (fun z => ε⁻¹ • z) hCf
    · calc
        (fderiv ℝ g u v).2.2 =
            (fderiv ℝ (fun z => (g z).2.2) u) v := hDg.symm
        _ = ε⁻¹ • (fderiv ℝ (fun z => (f z).2.2) u) v := by
          simpa only [smul_apply] using hd
        _ = ε⁻¹ • (fderiv ℝ f u v).2.2 :=
          congrArg (fun z => ε⁻¹ • z) hDf

end
end PhosphorylationStableCapacity
