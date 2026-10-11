module
public import proofs.PhosphorylationStableCapacity.ArbitrarySplitChartTotalDerivatives

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section

open PhosphorylationSharpness Polynomial

def arbitrarySplitChartU (y : ℝ) : ℝ := ratio y

def arbitrarySplitChartS (m : ℕ) (ξ : ℕ → ℝ)
    (r δ y : ℝ) : ℝ :=
  let u := arbitrarySplitChartU y
  let d := (arbitrarySplitRawD m ξ r δ).eval u
  let ell := (arbitrarySplitRawB m ξ r δ).eval u / d - r
  chartS u r ell d

def arbitrarySplitChartF (m : ℕ) (ξ : ℕ → ℝ)
    (r δ y : ℝ) : ℝ :=
  let u := arbitrarySplitChartU y
  let d := (arbitrarySplitRawD m ξ r δ).eval u
  let ell := (arbitrarySplitRawB m ξ r δ).eval u / d - r
  chartF u r ell

theorem arbitrarySplitChartState_eq_reconstruct
    (m : ℕ) (ξ : ℕ → ℝ) (r δ y : ℝ) :
    arbitrarySplitChartState m ξ r δ y =
      reconstruct
        (fun i : Fin (m+2) =>
          (((1+X)*arbitrarySplitRawD m ξ r δ : ℝ[X]).coeff i))
        (fun i : Fin (m+1) => (arbitrarySplitRawB m ξ r δ).coeff i)
        (fun i : Fin (m+1) => (arbitrarySplitRawD m ξ r δ).coeff i)
        (arbitrarySplitChartU y)
        (arbitrarySplitChartS m ξ r δ y)
        (arbitrarySplitChartF m ξ r δ y) := rfl

theorem arbitrarySplitChartU_hasDerivAt (y : ℝ) :
    HasDerivAt arbitrarySplitChartU (y/4) y := by
  unfold arbitrarySplitChartU ratio
  convert ((((hasDerivAt_id y).pow 2).sub
    (hasDerivAt_const y (1 : ℝ))).div_const (8 : ℝ)) using 1
  all_goals
    try funext z
    try simp
    try ring

theorem arbitrarySplitChartS_differentiableAt
    (m : ℕ) (ξ : ℕ → ℝ) (r δ y : ℝ)
    (hu : arbitrarySplitChartU y ≠ 0)
    (hd : (arbitrarySplitRawD m ξ r δ).eval (arbitrarySplitChartU y) ≠ 0)
    (hell : (arbitrarySplitRawB m ξ r δ).eval (arbitrarySplitChartU y) /
      (arbitrarySplitRawD m ξ r δ).eval (arbitrarySplitChartU y) - r ≠ 0) :
    DifferentiableAt ℝ (arbitrarySplitChartS m ξ r δ) y := by
  unfold arbitrarySplitChartS chartS arbitrarySplitChartU ratio
  fun_prop (disch := positivity)

theorem arbitrarySplitChartF_differentiableAt
    (m : ℕ) (ξ : ℕ → ℝ) (r δ y : ℝ)
    (hd : (arbitrarySplitRawD m ξ r δ).eval (arbitrarySplitChartU y) ≠ 0)
    (hellv : (arbitrarySplitRawB m ξ r δ).eval (arbitrarySplitChartU y) /
      (arbitrarySplitRawD m ξ r δ).eval (arbitrarySplitChartU y) -
        arbitrarySplitChartU y ≠ 0) :
    DifferentiableAt ℝ (arbitrarySplitChartF m ξ r δ) y := by
  have hden :
      ((arbitrarySplitRawB m ξ r δ).eval (arbitrarySplitChartU y) /
          (arbitrarySplitRawD m ξ r δ).eval (arbitrarySplitChartU y) - r) +
        (r - arbitrarySplitChartU y) ≠ 0 := by
    convert hellv using 1
    ring
  dsimp only [arbitrarySplitChartU, ratio] at hden hd
  unfold arbitrarySplitChartF chartF arbitrarySplitChartU ratio
  fun_prop (disch := assumption)

end
end PhosphorylationStableCapacity
