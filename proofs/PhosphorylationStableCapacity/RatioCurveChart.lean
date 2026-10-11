module
public import proofs.PhosphorylationStableCapacity.RatioCurveDerivative
public import proofs.PhosphorylationStableCapacity.Jacobian

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section
open PhosphorylationSharpness

/-- The equilibrium curve in the ordered `3n` free class variables. -/
def ratioEquilibriumCurveChart {n : ℕ} (k : Rates n)
    (FT ST u : ℝ) : CoordinateSpace n :=
  toCoordinateSpace (chart (ratioEquilibriumCurve k FT ST u))

theorem ratioEquilibriumCurveChart_differentiableAt {n : ℕ}
    (hn : 0 < n) (k : Rates n) (hk : k.Positive)
    (FT ST u : ℝ) (hST : 0 < ST) (hu : 0 < u) :
    DifferentiableAt ℝ (ratioEquilibriumCurveChart k FT ST) u := by
  have hs := modelRatioSubstrateLevel_differentiableAt
    hn k hk FT ST u hST hu
  have hf := ratioCurveFreePhosphatase_differentiableAt
    hn k hk FT ST u hST hu
  unfold ratioEquilibriumCurveChart ratioEquilibriumCurve
    ratioProfileState toCoordinateSpace chart
  dsimp
  fun_prop (disch := assumption)

end
end PhosphorylationStableCapacity
