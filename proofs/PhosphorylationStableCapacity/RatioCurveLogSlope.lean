module
public import proofs.PhosphorylationStableCapacity.RatioCurveDerivative

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section
open PhosphorylationSharpness

/-- Product rule for a varying amplitude times a monomial, expressed
in log-ratio coordinates without differentiating a logarithm. -/
theorem monomial_scaled_deriv
    (A : ℝ) (g : ℝ → ℝ) (m : ℕ) (u a d : ℝ)
    (hg : HasDerivAt g d u) (hga : u*d = g u*a) :
    u * deriv (fun v : ℝ => A*g v*v^m) u =
      (A*g u*u^m)*(a+(m:ℝ)) := by
  cases m with
  | zero =>
      have h := (hg.const_mul A).deriv
      simp only [pow_zero, mul_one, Nat.cast_zero, add_zero]
      rw [h]
      calc
        u*(A*d) = A*(u*d) := by ring
        _ = A*(g u*a) := by rw [hga]
        _ = (A*g u)*a := by ring
  | succ m =>
      have hp := hasDerivAt_pow (m+1) u
      have h := ((hg.const_mul A).mul hp).deriv
      have heq : m+1-1=m := by omega
      have h' : deriv (fun v : ℝ => A*g v*v^(m+1)) u =
          A*d*u^(m+1) + A*g u*((m+1:ℕ):ℝ)*u^m := by
        have hfun : (fun v : ℝ => A*g v*v^(m+1)) =
            (fun v : ℝ => A*g v) * (fun v : ℝ => v^(m+1)) := by
          funext v
          change A*g v*v^(m+1) = (A*g v)*v^(m+1)
          ring
        rw [hfun]
        simpa only [heq, mul_assoc] using h
      rw [h']
      linear_combination A*u^(m+1)*hga

theorem product_scaled_deriv
    (f g : ℝ → ℝ) (u a b df dg : ℝ)
    (hf : HasDerivAt f df u) (hg : HasDerivAt g dg u)
    (hfa : u*df = f u*a) (hgb : u*dg = g u*b) :
    u*deriv (fun v => f v*g v) u = f u*g u*(a+b) := by
  have hfun : (fun v => f v*g v) = f*g := by
    funext v
    rfl
  rw [hfun]
  rw [(hf.mul hg).deriv]
  linear_combination (g u)*hfa + (f u)*hgb

def ratioCurveSubstrateLogSlope {n : ℕ} (k : Rates n)
    (FT ST u : ℝ) : ℝ :=
  u * deriv (modelRatioSubstrateLevel k FT ST) u /
    modelRatioSubstrateLevel k FT ST u

def ratioCurvePhosphataseLogSlope {n : ℕ} (k : Rates n)
    (FT ST u : ℝ) : ℝ :=
  u * deriv (ratioCurveFreePhosphatase k FT ST) u /
    ratioCurveFreePhosphatase k FT ST u

theorem ratioCurveSubstrate_log_slope_eq {n : ℕ}
    (hn : 0 < n) (k : Rates n) (hk : k.Positive)
    (FT ST u : ℝ) (hST : 0 < ST) (hu : 0 < u) :
    u*deriv (modelRatioSubstrateLevel k FT ST) u =
      modelRatioSubstrateLevel k FT ST u *
        ratioCurveSubstrateLogSlope k FT ST u := by
  have hs := (modelRatioSubstrateLevel_pos_and_inventory
    hn k hk FT ST u hST hu).1
  dsimp [ratioCurveSubstrateLogSlope]
  field_simp [ne_of_gt hs]

theorem ratioCurvePhosphatase_log_slope_eq {n : ℕ}
    (hn : 0 < n) (k : Rates n) (hk : k.Positive)
    (FT ST u : ℝ) (hFT : 0 < FT) (hST : 0 < ST)
    (hu : 0 < u) :
    u*deriv (ratioCurveFreePhosphatase k FT ST) u =
      ratioCurveFreePhosphatase k FT ST u *
        ratioCurvePhosphataseLogSlope k FT ST u := by
  have hs := (modelRatioSubstrateLevel_pos_and_inventory
    hn k hk FT ST u hST hu).1
  have hD := phosphataseComplexInventory_pos k hk hu hn
  have hden : 0 < 1 + modelRatioSubstrateLevel k FT ST u *
      phosphataseComplexInventory k u := by
    nlinarith [mul_pos hs hD]
  have hf : 0 < ratioCurveFreePhosphatase k FT ST u :=
    div_pos hFT hden
  dsimp [ratioCurvePhosphataseLogSlope]
  field_simp [ne_of_gt hf]

end
end PhosphorylationStableCapacity
