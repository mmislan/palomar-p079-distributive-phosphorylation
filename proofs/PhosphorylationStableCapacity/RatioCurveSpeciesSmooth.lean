module
public import proofs.PhosphorylationStableCapacity.RatioCurveSpeciesLogDerivative

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section
open PhosphorylationSharpness

theorem ratioCurve_substrate_differentiableAt {n : ℕ}
    (hn : 0 < n) (k : Rates n) (hk : k.Positive)
    (FT ST u : ℝ) (hST : 0 < ST) (hu : 0 < u)
    (j : Fin (n+1)) :
    DifferentiableAt ℝ
      (fun v => (ratioEquilibriumCurve k FT ST v).S j) u := by
  have hs := modelRatioSubstrateLevel_differentiableAt
    hn k hk FT ST u hST hu
  unfold ratioEquilibriumCurve ratioProfileState
  dsimp
  fun_prop (disch := assumption)

theorem ratioCurve_kinase_differentiableAt {n : ℕ}
    (hn : 0 < n) (k : Rates n) (hk : k.Positive)
    (FT ST u : ℝ) (hST : 0 < ST) (hu : 0 < u) :
    DifferentiableAt ℝ
      (fun v => (ratioEquilibriumCurve k FT ST v).E) u := by
  have hf := ratioCurveFreePhosphatase_differentiableAt
    hn k hk FT ST u hST hu
  unfold ratioEquilibriumCurve ratioProfileState
  dsimp
  fun_prop (disch := assumption)

theorem ratioCurve_phosphatase_differentiableAt {n : ℕ}
    (hn : 0 < n) (k : Rates n) (hk : k.Positive)
    (FT ST u : ℝ) (hST : 0 < ST) (hu : 0 < u) :
    DifferentiableAt ℝ
      (fun v => (ratioEquilibriumCurve k FT ST v).F) u := by
  exact ratioCurveFreePhosphatase_differentiableAt
    hn k hk FT ST u hST hu

theorem ratioCurve_kinaseComplex_differentiableAt {n : ℕ}
    (hn : 0 < n) (k : Rates n) (hk : k.Positive)
    (FT ST u : ℝ) (hST : 0 < ST) (hu : 0 < u)
    (i : Fin n) :
    DifferentiableAt ℝ
      (fun v => (ratioEquilibriumCurve k FT ST v).C i) u := by
  have hs := modelRatioSubstrateLevel_differentiableAt
    hn k hk FT ST u hST hu
  have hf := ratioCurveFreePhosphatase_differentiableAt
    hn k hk FT ST u hST hu
  unfold ratioEquilibriumCurve ratioProfileState
  dsimp
  fun_prop (disch := assumption)

theorem ratioCurve_phosphataseComplex_differentiableAt {n : ℕ}
    (hn : 0 < n) (k : Rates n) (hk : k.Positive)
    (FT ST u : ℝ) (hST : 0 < ST) (hu : 0 < u)
    (i : Fin n) :
    DifferentiableAt ℝ
      (fun v => (ratioEquilibriumCurve k FT ST v).D i) u := by
  have hs := modelRatioSubstrateLevel_differentiableAt
    hn k hk FT ST u hST hu
  have hf := ratioCurveFreePhosphatase_differentiableAt
    hn k hk FT ST u hST hu
  unfold ratioEquilibriumCurve ratioProfileState
  dsimp
  fun_prop (disch := assumption)

end
end PhosphorylationStableCapacity
