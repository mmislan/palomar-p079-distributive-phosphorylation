module
public import proofs.PhosphorylationStableCapacity.FiniteThreeSiteJacobianRows

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section
open PhosphorylationSharpness Module

set_option maxHeartbeats 2000000

theorem threeSiteS1_hasFDerivAt (ET FT : ℝ)
    (k : Rates 3) (u : CoordinateSpace 3) :
    HasFDerivAt
      (fun v : CoordinateSpace 3 =>
        k.c 0 * v.2.1 0 -
          k.alpha 0 * v.1 0 * threeSiteFreeF FT v +
          k.beta 0 * v.2.2 0 -
          k.a 1 * v.1 0 * threeSiteFreeE ET v +
          k.b 1 * v.2.1 1 +
          k.gamma 1 * v.2.2 1)
      (k.c 0 • threeSitePC 0 -
        k.alpha 0 •
          (threeSiteFreeF FT u • threeSitePS 0 +
            u.1 0 • threeSiteFLinear) +
        k.beta 0 • threeSitePD 0 -
        k.a 1 •
          (threeSiteFreeE ET u • threeSitePS 0 +
            u.1 0 • threeSiteELinear) +
        k.b 1 • threeSitePC 1 +
        k.gamma 1 • threeSitePD 1) u := by
  have hs : HasFDerivAt (fun v : CoordinateSpace 3 => v.1 0)
      (threeSitePS 0) u := (threeSitePS 0).hasFDerivAt
  have hc0 : HasFDerivAt (fun v : CoordinateSpace 3 => v.2.1 0)
      (threeSitePC 0) u := (threeSitePC 0).hasFDerivAt
  have hc1 : HasFDerivAt (fun v : CoordinateSpace 3 => v.2.1 1)
      (threeSitePC 1) u := (threeSitePC 1).hasFDerivAt
  have hd0 : HasFDerivAt (fun v : CoordinateSpace 3 => v.2.2 0)
      (threeSitePD 0) u := (threeSitePD 0).hasFDerivAt
  have hd1 : HasFDerivAt (fun v : CoordinateSpace 3 => v.2.2 1)
      (threeSitePD 1) u := (threeSitePD 1).hasFDerivAt
  let fcalc : CoordinateSpace 3 → ℝ := fun v =>
    (((((k.c 0 * v.2.1 0 - k.alpha 0 * (v.1 0 * threeSiteFreeF FT v)) +
      k.beta 0 * v.2.2 0) - k.a 1 * (v.1 0 * threeSiteFreeE ET v)) +
      k.b 1 * v.2.1 1) + k.gamma 1 * v.2.2 1)
  let Dcalc : CoordinateSpace 3 →L[ℝ] ℝ :=
    (((((k.c 0 • threeSitePC 0 -
      k.alpha 0 • (u.1 0 • threeSiteFLinear +
        threeSiteFreeF FT u • threeSitePS 0)) +
      k.beta 0 • threeSitePD 0) -
      k.a 1 • (u.1 0 • threeSiteELinear +
        threeSiteFreeE ET u • threeSitePS 0)) +
      k.b 1 • threeSitePC 1) + k.gamma 1 • threeSitePD 1)
  have hcalc : HasFDerivAt fcalc Dcalc u := by
    exact ((((((hc0.const_mul (k.c 0)).sub
      ((hs.mul (threeSiteFreeF_hasFDerivAt FT u)).const_mul
        (k.alpha 0))).add (hd0.const_mul (k.beta 0))).sub
      ((hs.mul (threeSiteFreeE_hasFDerivAt ET u)).const_mul
        (k.a 1))).add (hc1.const_mul (k.b 1))).add
      (hd1.const_mul (k.gamma 1)))
  have hf : fcalc = (fun v : CoordinateSpace 3 =>
      k.c 0 * v.2.1 0 - k.alpha 0 * v.1 0 * threeSiteFreeF FT v +
      k.beta 0 * v.2.2 0 - k.a 1 * v.1 0 * threeSiteFreeE ET v +
      k.b 1 * v.2.1 1 + k.gamma 1 * v.2.2 1) := by
    funext v
    dsimp [fcalc]
    ring
  have hD : Dcalc =
      k.c 0 • threeSitePC 0 -
        k.alpha 0 • (threeSiteFreeF FT u • threeSitePS 0 +
          u.1 0 • threeSiteFLinear) +
        k.beta 0 • threeSitePD 0 -
        k.a 1 • (threeSiteFreeE ET u • threeSitePS 0 +
          u.1 0 • threeSiteELinear) +
        k.b 1 • threeSitePC 1 + k.gamma 1 • threeSitePD 1 := by
    apply ContinuousLinearMap.ext
    intro v
    simp [Dcalc]
    ring
  rw [hf, hD] at hcalc
  exact hcalc



theorem threeSiteS2_hasFDerivAt (ET FT : ℝ)
    (k : Rates 3) (u : CoordinateSpace 3) :
    HasFDerivAt
      (fun v : CoordinateSpace 3 =>
        k.c 1 * v.2.1 1 -
          k.alpha 1 * v.1 1 * threeSiteFreeF FT v +
          k.beta 1 * v.2.2 1 -
          k.a 2 * v.1 1 * threeSiteFreeE ET v +
          k.b 2 * v.2.1 2 +
          k.gamma 2 * v.2.2 2)
      (k.c 1 • threeSitePC 1 -
        k.alpha 1 •
          (threeSiteFreeF FT u • threeSitePS 1 +
            u.1 1 • threeSiteFLinear) +
        k.beta 1 • threeSitePD 1 -
        k.a 2 •
          (threeSiteFreeE ET u • threeSitePS 1 +
            u.1 1 • threeSiteELinear) +
        k.b 2 • threeSitePC 2 +
        k.gamma 2 • threeSitePD 2) u := by
  have hs : HasFDerivAt (fun v : CoordinateSpace 3 => v.1 1)
      (threeSitePS 1) u := (threeSitePS 1).hasFDerivAt
  have hc0 : HasFDerivAt (fun v : CoordinateSpace 3 => v.2.1 1)
      (threeSitePC 1) u := (threeSitePC 1).hasFDerivAt
  have hc1 : HasFDerivAt (fun v : CoordinateSpace 3 => v.2.1 2)
      (threeSitePC 2) u := (threeSitePC 2).hasFDerivAt
  have hd0 : HasFDerivAt (fun v : CoordinateSpace 3 => v.2.2 1)
      (threeSitePD 1) u := (threeSitePD 1).hasFDerivAt
  have hd1 : HasFDerivAt (fun v : CoordinateSpace 3 => v.2.2 2)
      (threeSitePD 2) u := (threeSitePD 2).hasFDerivAt
  let fcalc : CoordinateSpace 3 → ℝ := fun v =>
    (((((k.c 1 * v.2.1 1 - k.alpha 1 * (v.1 1 * threeSiteFreeF FT v)) +
      k.beta 1 * v.2.2 1) - k.a 2 * (v.1 1 * threeSiteFreeE ET v)) +
      k.b 2 * v.2.1 2) + k.gamma 2 * v.2.2 2)
  let Dcalc : CoordinateSpace 3 →L[ℝ] ℝ :=
    (((((k.c 1 • threeSitePC 1 -
      k.alpha 1 • (u.1 1 • threeSiteFLinear +
        threeSiteFreeF FT u • threeSitePS 1)) +
      k.beta 1 • threeSitePD 1) -
      k.a 2 • (u.1 1 • threeSiteELinear +
        threeSiteFreeE ET u • threeSitePS 1)) +
      k.b 2 • threeSitePC 2) + k.gamma 2 • threeSitePD 2)
  have hcalc : HasFDerivAt fcalc Dcalc u := by
    exact ((((((hc0.const_mul (k.c 1)).sub
      ((hs.mul (threeSiteFreeF_hasFDerivAt FT u)).const_mul
        (k.alpha 1))).add (hd0.const_mul (k.beta 1))).sub
      ((hs.mul (threeSiteFreeE_hasFDerivAt ET u)).const_mul
        (k.a 2))).add (hc1.const_mul (k.b 2))).add
      (hd1.const_mul (k.gamma 2)))
  have hf : fcalc = (fun v : CoordinateSpace 3 =>
      k.c 1 * v.2.1 1 - k.alpha 1 * v.1 1 * threeSiteFreeF FT v +
      k.beta 1 * v.2.2 1 - k.a 2 * v.1 1 * threeSiteFreeE ET v +
      k.b 2 * v.2.1 2 + k.gamma 2 * v.2.2 2) := by
    funext v
    dsimp [fcalc]
    ring
  have hD : Dcalc =
      k.c 1 • threeSitePC 1 -
        k.alpha 1 • (threeSiteFreeF FT u • threeSitePS 1 +
          u.1 1 • threeSiteFLinear) +
        k.beta 1 • threeSitePD 1 -
        k.a 2 • (threeSiteFreeE ET u • threeSitePS 1 +
          u.1 1 • threeSiteELinear) +
        k.b 2 • threeSitePC 2 + k.gamma 2 • threeSitePD 2 := by
    apply ContinuousLinearMap.ext
    intro v
    simp [Dcalc]
    ring
  rw [hf, hD] at hcalc
  exact hcalc


end
end PhosphorylationStableCapacity
