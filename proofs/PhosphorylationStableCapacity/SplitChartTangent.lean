module
public import proofs.PhosphorylationStableCapacity.ReconstructCurveOrientation
public import proofs.PhosphorylationStableCapacity.SplitChartDerivative

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section
open PhosphorylationSharpness Polynomial

def splitChartU (y : ℝ) : ℝ := ratio y

def splitChartS (m : ℕ) (r δ y : ℝ) : ℝ :=
  let u := splitChartU y
  let d := (splitRawD m r δ).eval u
  let ell := (splitRawB m r δ).eval u / d - r
  chartS u r ell d

def splitChartF (m : ℕ) (r δ y : ℝ) : ℝ :=
  let u := splitChartU y
  let d := (splitRawD m r δ).eval u
  let ell := (splitRawB m r δ).eval u / d - r
  chartF u r ell

theorem splitChartState_eq_reconstruct (m : ℕ) (r δ y : ℝ) :
    splitChartState m r δ y =
      reconstruct
        (fun i : Fin (m+2) =>
          (((1+X)*splitRawD m r δ : ℝ[X]).coeff i))
        (fun i : Fin (m+1) => (splitRawB m r δ).coeff i)
        (fun i : Fin (m+1) => (splitRawD m r δ).coeff i)
        (splitChartU y) (splitChartS m r δ y)
        (splitChartF m r δ y) := rfl

theorem splitChartU_hasDerivAt (y : ℝ) :
    HasDerivAt splitChartU (y/4) y := by
  unfold splitChartU ratio
  convert ((((hasDerivAt_id y).pow 2).sub
    (hasDerivAt_const y (1 : ℝ))).div_const (8 : ℝ)) using 1
  all_goals
    try funext z
    try simp
    try ring

theorem splitChartS_differentiableAt (m : ℕ) (r δ y : ℝ)
    (hu : splitChartU y ≠ 0)
    (hd : (splitRawD m r δ).eval (splitChartU y) ≠ 0)
    (hell : (splitRawB m r δ).eval (splitChartU y) /
      (splitRawD m r δ).eval (splitChartU y) - r ≠ 0) :
    DifferentiableAt ℝ (splitChartS m r δ) y := by
  unfold splitChartS chartS splitChartU ratio
  fun_prop (disch := positivity)

theorem splitChartF_differentiableAt (m : ℕ) (r δ y : ℝ)
    (hd : (splitRawD m r δ).eval (splitChartU y) ≠ 0)
    (hellv : (splitRawB m r δ).eval (splitChartU y) /
      (splitRawD m r δ).eval (splitChartU y) - splitChartU y ≠ 0) :
    DifferentiableAt ℝ (splitChartF m r δ) y := by
  have hden :
      ((splitRawB m r δ).eval (splitChartU y) /
          (splitRawD m r δ).eval (splitChartU y) - r) +
        (r - splitChartU y) ≠ 0 := by
    convert hellv using 1
    ring
  dsimp only [splitChartU, ratio] at hden hd
  unfold splitChartF chartF splitChartU ratio
  fun_prop (disch := assumption)

end
end PhosphorylationStableCapacity
