module
public import proofs.PhosphorylationStableCapacity.RatioCurveLogSlope

@[expose] public section
set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

namespace PhosphorylationStableCapacity

noncomputable section
open PhosphorylationSharpness

/-- Each free substrate concentration has logarithmic ratio slope
equal to the common substrate amplitude slope plus its site index. -/
theorem ratioCurve_substrate_scaled_deriv {n : ℕ}
    (hn : 0 < n) (k : Rates n) (hk : k.Positive)
    (FT ST u : ℝ) (hST : 0 < ST) (hu : 0 < u)
    (j : Fin (n+1)) :
    u*deriv (fun v => (ratioEquilibriumCurve k FT ST v).S j) u =
      (ratioEquilibriumCurve k FT ST u).S j *
        (ratioCurveSubstrateLogSlope k FT ST u + (j.val:ℝ)) := by
  let s := modelRatioSubstrateLevel k FT ST
  let a := ratioCurveSubstrateLogSlope k FT ST u
  have hs : DifferentiableAt ℝ s u :=
    modelRatioSubstrateLevel_differentiableAt hn k hk FT ST u hST hu
  have hsa : u*deriv s u = s u*a :=
    ratioCurveSubstrate_log_slope_eq hn k hk FT ST u hST hu
  have h := monomial_scaled_deriv
    (equilibriumWeight k j.val) s j.val u a (deriv s u)
    hs.hasDerivAt hsa
  have hfun : (fun v => (ratioEquilibriumCurve k FT ST v).S j) =
      (fun v => equilibriumWeight k j.val*s v*v^j.val) := by
    funext v
    simp [ratioEquilibriumCurve, ratioProfileState, s]
    ring
  rw [hfun]
  simpa only [ratioEquilibriumCurve, ratioProfileState, s, a,
    mul_assoc, mul_left_comm, mul_comm] using h

theorem ratioCurve_phosphatase_scaled_deriv {n : ℕ}
    (hn : 0 < n) (k : Rates n) (hk : k.Positive)
    (FT ST u : ℝ) (hFT : 0 < FT) (hST : 0 < ST)
    (hu : 0 < u) :
    u*deriv (fun v => (ratioEquilibriumCurve k FT ST v).F) u =
      (ratioEquilibriumCurve k FT ST u).F *
        ratioCurvePhosphataseLogSlope k FT ST u := by
  let f := ratioCurveFreePhosphatase k FT ST
  let b := ratioCurvePhosphataseLogSlope k FT ST u
  have hf : DifferentiableAt ℝ f u :=
    ratioCurveFreePhosphatase_differentiableAt
      hn k hk FT ST u hST hu
  have hfb : u*deriv f u = f u*b :=
    ratioCurvePhosphatase_log_slope_eq
      hn k hk FT ST u hFT hST hu
  have h := monomial_scaled_deriv 1 f 0 u b (deriv f u)
    hf.hasDerivAt hfb
  simpa [ratioEquilibriumCurve, ratioProfileState, f, b] using h

theorem ratioCurve_kinase_scaled_deriv {n : ℕ}
    (hn : 0 < n) (k : Rates n) (hk : k.Positive)
    (FT ST u : ℝ) (hFT : 0 < FT) (hST : 0 < ST)
    (hu : 0 < u) :
    u*deriv (fun v => (ratioEquilibriumCurve k FT ST v).E) u =
      (ratioEquilibriumCurve k FT ST u).E *
        (1 + ratioCurvePhosphataseLogSlope k FT ST u) := by
  let f := ratioCurveFreePhosphatase k FT ST
  let b := ratioCurvePhosphataseLogSlope k FT ST u
  have hf : DifferentiableAt ℝ f u :=
    ratioCurveFreePhosphatase_differentiableAt
      hn k hk FT ST u hST hu
  have hfb : u*deriv f u = f u*b :=
    ratioCurvePhosphatase_log_slope_eq
      hn k hk FT ST u hFT hST hu
  have h := monomial_scaled_deriv 1 f 1 u b (deriv f u)
    hf.hasDerivAt hfb
  have hfun : (fun v => (ratioEquilibriumCurve k FT ST v).E) =
      (fun v => f v*v) := by
    funext v
    simp [ratioEquilibriumCurve, ratioProfileState, f]
    ring
  rw [hfun]
  change u*deriv (fun v => f v*v) u = (u*f u)*(1+b)
  calc
    _ = (f u*u)*(b+1) := by simpa using h
    _ = (u*f u)*(1+b) := by ring

private theorem ratioCurve_complex_scaled_deriv_aux {n : ℕ}
    (hn : 0 < n) (k : Rates n) (hk : k.Positive)
    (FT ST u A : ℝ) (hFT : 0 < FT) (hST : 0 < ST)
    (hu : 0 < u) (m : ℕ) :
    let f := ratioCurveFreePhosphatase k FT ST
    let s := modelRatioSubstrateLevel k FT ST
    let a := ratioCurveSubstrateLogSlope k FT ST u
    let b := ratioCurvePhosphataseLogSlope k FT ST u
    u*deriv (fun v => f v*s v*A*v^m) u =
      (f u*s u*A*u^m)*(a+b+(m:ℝ)) := by
  dsimp only
  let f := ratioCurveFreePhosphatase k FT ST
  let s := modelRatioSubstrateLevel k FT ST
  let a := ratioCurveSubstrateLogSlope k FT ST u
  let b := ratioCurvePhosphataseLogSlope k FT ST u
  have hf : DifferentiableAt ℝ f u :=
    ratioCurveFreePhosphatase_differentiableAt
      hn k hk FT ST u hST hu
  have hs : DifferentiableAt ℝ s u :=
    modelRatioSubstrateLevel_differentiableAt
      hn k hk FT ST u hST hu
  have hfb : u*deriv f u = f u*b :=
    ratioCurvePhosphatase_log_slope_eq
      hn k hk FT ST u hFT hST hu
  have hsa : u*deriv s u = s u*a :=
    ratioCurveSubstrate_log_slope_eq hn k hk FT ST u hST hu
  have hprod := product_scaled_deriv f s u b a
    (deriv f u) (deriv s u) hf.hasDerivAt hs.hasDerivAt hfb hsa
  let g : ℝ → ℝ := fun v => f v*s v
  have hg : HasDerivAt g (deriv g u) u :=
    (hf.mul hs).hasDerivAt
  have h := monomial_scaled_deriv A g m u (b+a) (deriv g u)
    hg hprod
  have hfun : (fun v => f v*s v*A*v^m) =
      (fun v => A*g v*v^m) := by
    funext v
    dsimp [g]
    ring
  rw [hfun]
  convert h using 1
  ring

/-- Both literal complex families share the same log-ratio slope at
their associated product substrate level. -/
theorem ratioCurve_kinaseComplex_scaled_deriv {n : ℕ}
    (hn : 0 < n) (k : Rates n) (hk : k.Positive)
    (FT ST u : ℝ) (hFT : 0 < FT) (hST : 0 < ST)
    (hu : 0 < u) (i : Fin n) :
    u*deriv (fun v => (ratioEquilibriumCurve k FT ST v).C i) u =
      (ratioEquilibriumCurve k FT ST u).C i *
        (ratioCurveSubstrateLogSlope k FT ST u +
          ratioCurvePhosphataseLogSlope k FT ST u +
          ((i.val+1:ℕ):ℝ)) := by
  have h := ratioCurve_complex_scaled_deriv_aux
    hn k hk FT ST u
    (kinaseBindingRatio k i * equilibriumWeight k i.val)
    hFT hST hu (i.val+1)
  have hfun : (fun v => (ratioEquilibriumCurve k FT ST v).C i) =
      (fun v => ratioCurveFreePhosphatase k FT ST v *
        modelRatioSubstrateLevel k FT ST v *
        (kinaseBindingRatio k i * equilibriumWeight k i.val) *
        v^(i.val+1)) := by
    funext v
    change ratioCurveFreePhosphatase k FT ST v *
      modelRatioSubstrateLevel k FT ST v *
      kinaseBindingRatio k i * equilibriumWeight k i.val *
      v^(i.val+1) = _
    ring
  rw [hfun]
  simpa only [ratioEquilibriumCurve, ratioProfileState,
    mul_assoc, mul_left_comm, mul_comm] using h

theorem ratioCurve_phosphataseComplex_scaled_deriv {n : ℕ}
    (hn : 0 < n) (k : Rates n) (hk : k.Positive)
    (FT ST u : ℝ) (hFT : 0 < FT) (hST : 0 < ST)
    (hu : 0 < u) (i : Fin n) :
    u*deriv (fun v => (ratioEquilibriumCurve k FT ST v).D i) u =
      (ratioEquilibriumCurve k FT ST u).D i *
        (ratioCurveSubstrateLogSlope k FT ST u +
          ratioCurvePhosphataseLogSlope k FT ST u +
          ((i.val+1:ℕ):ℝ)) := by
  have h := ratioCurve_complex_scaled_deriv_aux
    hn k hk FT ST u
    (phosphataseBindingRatio k i * equilibriumWeight k (i.val+1))
    hFT hST hu (i.val+1)
  have hfun : (fun v => (ratioEquilibriumCurve k FT ST v).D i) =
      (fun v => ratioCurveFreePhosphatase k FT ST v *
        modelRatioSubstrateLevel k FT ST v *
        (phosphataseBindingRatio k i * equilibriumWeight k (i.val+1)) *
        v^(i.val+1)) := by
    funext v
    change ratioCurveFreePhosphatase k FT ST v *
      modelRatioSubstrateLevel k FT ST v *
      phosphataseBindingRatio k i * equilibriumWeight k (i.val+1) *
      v^(i.val+1) = _
    ring
  rw [hfun]
  simpa only [ratioEquilibriumCurve, ratioProfileState,
    mul_assoc, mul_left_comm, mul_comm] using h

end
end PhosphorylationStableCapacity
