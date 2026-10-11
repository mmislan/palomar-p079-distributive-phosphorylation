module
public import proofs.PhosphorylationStableCapacity.FiniteThreeSiteJacobianDefinitions

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section
open PhosphorylationSharpness Module

set_option maxHeartbeats 2000000

theorem threeSiteD_hasFDerivAt (i : Fin 3) (FT : ℝ) (k : Rates 3)
    (u : CoordinateSpace 3) :
    HasFDerivAt
      (fun v : CoordinateSpace 3 =>
        k.alpha i * v.1 i * threeSiteFreeF FT v -
          (k.beta i + k.gamma i) * v.2.2 i)
      (k.alpha i • (threeSiteFreeF FT u • threeSitePS i +
          u.1 i • threeSiteFLinear) -
        (k.beta i + k.gamma i) • threeSitePD i) u := by
  have hs : HasFDerivAt (fun v : CoordinateSpace 3 => v.1 i)
      (threeSitePS i) u := (threeSitePS i).hasFDerivAt
  have hd : HasFDerivAt (fun v : CoordinateSpace 3 => v.2.2 i)
      (threeSitePD i) u := (threeSitePD i).hasFDerivAt
  convert (((hs.mul (threeSiteFreeF_hasFDerivAt FT u)).const_mul
    (k.alpha i)).sub (hd.const_mul (k.beta i + k.gamma i))) using 1
  · funext v
    simp
    ring
  · apply ContinuousLinearMap.ext
    intro v
    simp
    ring

theorem threeSiteC0_hasFDerivAt (ET ST : ℝ) (k : Rates 3)
    (u : CoordinateSpace 3) :
    HasFDerivAt
      (fun v : CoordinateSpace 3 =>
        k.a 0 * threeSiteFreeS0 ST v * threeSiteFreeE ET v -
          (k.b 0 + k.c 0) * v.2.1 0)
      (threeSiteRowC0 ET ST k u) u := by
  have hc : HasFDerivAt (fun v : CoordinateSpace 3 => v.2.1 0)
      (threeSitePC 0) u := (threeSitePC 0).hasFDerivAt
  convert (((threeSiteFreeS0_hasFDerivAt ST u).mul
    (threeSiteFreeE_hasFDerivAt ET u)).const_mul
    (k.a 0)).sub (hc.const_mul (k.b 0 + k.c 0)) using 1
  · funext v
    simp
    ring
  · apply ContinuousLinearMap.ext
    intro v
    simp [threeSiteRowC0]
    ring

theorem threeSiteCSucc_hasFDerivAt (i : Fin 2) (ET : ℝ)
    (k : Rates 3) (u : CoordinateSpace 3) :
    HasFDerivAt
      (fun v : CoordinateSpace 3 =>
        k.a i.succ * v.1 i.castSucc * threeSiteFreeE ET v -
          (k.b i.succ + k.c i.succ) * v.2.1 i.succ)
      (k.a i.succ • (threeSiteFreeE ET u • threeSitePS i.castSucc +
          u.1 i.castSucc • threeSiteELinear) -
        (k.b i.succ + k.c i.succ) • threeSitePC i.succ) u := by
  have hs : HasFDerivAt (fun v : CoordinateSpace 3 => v.1 i.castSucc)
      (threeSitePS i.castSucc) u := (threeSitePS i.castSucc).hasFDerivAt
  have hc : HasFDerivAt (fun v : CoordinateSpace 3 => v.2.1 i.succ)
      (threeSitePC i.succ) u := (threeSitePC i.succ).hasFDerivAt
  convert (((hs.mul (threeSiteFreeE_hasFDerivAt ET u)).const_mul
    (k.a i.succ)).sub (hc.const_mul (k.b i.succ + k.c i.succ))) using 1
  · funext v
    simp
    ring
  · apply ContinuousLinearMap.ext
    intro v
    simp
    ring

theorem threeSiteS3_hasFDerivAt (FT : ℝ) (k : Rates 3)
    (u : CoordinateSpace 3) :
    HasFDerivAt
      (fun v : CoordinateSpace 3 =>
        k.c 2 * v.2.1 2 - k.alpha 2 * v.1 2 * threeSiteFreeF FT v +
          k.beta 2 * v.2.2 2)
      (threeSiteRowS3 FT k u) u := by
  have hs : HasFDerivAt (fun v : CoordinateSpace 3 => v.1 2)
      (threeSitePS 2) u := (threeSitePS 2).hasFDerivAt
  have hc : HasFDerivAt (fun v : CoordinateSpace 3 => v.2.1 2)
      (threeSitePC 2) u := (threeSitePC 2).hasFDerivAt
  have hd : HasFDerivAt (fun v : CoordinateSpace 3 => v.2.2 2)
      (threeSitePD 2) u := (threeSitePD 2).hasFDerivAt
  convert (((hc.const_mul (k.c 2)).sub
    ((hs.mul (threeSiteFreeF_hasFDerivAt FT u)).const_mul
      (k.alpha 2))).add (hd.const_mul (k.beta 2))) using 1
  · funext v
    simp
    ring
  · apply ContinuousLinearMap.ext
    intro v
    simp [threeSiteRowS3]
    ring


end
end PhosphorylationStableCapacity
