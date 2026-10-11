module
public import proofs.PhosphorylationStableCapacity.FiniteThreeSiteFieldFormula

@[expose] public section
set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

namespace PhosphorylationStableCapacity

noncomputable section
open PhosphorylationSharpness Module

private abbrev ThreePi := Fin 3 → ℝ

def threeSitePS (i : Fin 3) : CoordinateSpace 3 →L[ℝ] ℝ :=
  (ContinuousLinearMap.proj i).comp
    (ContinuousLinearMap.fst ℝ ThreePi (ThreePi × ThreePi))

def threeSitePC (i : Fin 3) : CoordinateSpace 3 →L[ℝ] ℝ :=
  (ContinuousLinearMap.proj i).comp
    ((ContinuousLinearMap.fst ℝ ThreePi ThreePi).comp
      (ContinuousLinearMap.snd ℝ ThreePi (ThreePi × ThreePi)))

def threeSitePD (i : Fin 3) : CoordinateSpace 3 →L[ℝ] ℝ :=
  (ContinuousLinearMap.proj i).comp
    ((ContinuousLinearMap.snd ℝ ThreePi ThreePi).comp
      (ContinuousLinearMap.snd ℝ ThreePi (ThreePi × ThreePi)))

@[simp] theorem threeSitePS_apply (i : Fin 3) (u : CoordinateSpace 3) :
    threeSitePS i u = u.1 i := rfl
@[simp] theorem threeSitePC_apply (i : Fin 3) (u : CoordinateSpace 3) :
    threeSitePC i u = u.2.1 i := rfl
@[simp] theorem threeSitePD_apply (i : Fin 3) (u : CoordinateSpace 3) :
    threeSitePD i u = u.2.2 i := rfl

def threeSiteS0Linear : CoordinateSpace 3 →L[ℝ] ℝ :=
  -threeSitePS 0 - threeSitePS 1 - threeSitePS 2 -
    threeSitePC 0 - threeSitePC 1 - threeSitePC 2 -
    threeSitePD 0 - threeSitePD 1 - threeSitePD 2

def threeSiteELinear : CoordinateSpace 3 →L[ℝ] ℝ :=
  -threeSitePC 0 - threeSitePC 1 - threeSitePC 2

def threeSiteFLinear : CoordinateSpace 3 →L[ℝ] ℝ :=
  -threeSitePD 0 - threeSitePD 1 - threeSitePD 2

theorem threeSiteFreeS0_hasFDerivAt (ST : ℝ) (u : CoordinateSpace 3) :
    HasFDerivAt (threeSiteFreeS0 ST) threeSiteS0Linear u := by
  convert (((((((((((threeSitePS 0).hasFDerivAt.const_sub ST).sub
    (threeSitePS 1).hasFDerivAt).sub (threeSitePS 2).hasFDerivAt).sub
    (threeSitePC 0).hasFDerivAt).sub (threeSitePC 1).hasFDerivAt).sub
    (threeSitePC 2).hasFDerivAt).sub (threeSitePD 0).hasFDerivAt).sub
    (threeSitePD 1).hasFDerivAt).sub (threeSitePD 2).hasFDerivAt)) using 1
  · funext v; simp [threeSiteFreeS0]
  · apply ContinuousLinearMap.ext
    intro v
    simp [threeSiteS0Linear]

theorem threeSiteFreeE_hasFDerivAt (ET : ℝ) (u : CoordinateSpace 3) :
    HasFDerivAt (threeSiteFreeE ET) threeSiteELinear u := by
  convert ((((threeSitePC 0).hasFDerivAt.const_sub ET).sub
    (threeSitePC 1).hasFDerivAt).sub (threeSitePC 2).hasFDerivAt) using 1
  · funext v; simp [threeSiteFreeE]
  · apply ContinuousLinearMap.ext
    intro v
    simp [threeSiteELinear]

theorem threeSiteFreeF_hasFDerivAt (FT : ℝ) (u : CoordinateSpace 3) :
    HasFDerivAt (threeSiteFreeF FT) threeSiteFLinear u := by
  convert ((((threeSitePD 0).hasFDerivAt.const_sub FT).sub
    (threeSitePD 1).hasFDerivAt).sub (threeSitePD 2).hasFDerivAt) using 1
  · funext v; simp [threeSiteFreeF]
  · apply ContinuousLinearMap.ext
    intro v
    simp [threeSiteFLinear]

def threeSiteRowS1 (ET FT : ℝ) (k : Rates 3)
    (u : CoordinateSpace 3) : CoordinateSpace 3 →L[ℝ] ℝ :=
  k.c 0 • threeSitePC 0 -
    k.alpha 0 • (threeSiteFreeF FT u • threeSitePS 0 + u.1 0 • threeSiteFLinear) +
    k.beta 0 • threeSitePD 0 -
    k.a 1 • (threeSiteFreeE ET u • threeSitePS 0 + u.1 0 • threeSiteELinear) +
    k.b 1 • threeSitePC 1 + k.gamma 1 • threeSitePD 1

def threeSiteRowS2 (ET FT : ℝ) (k : Rates 3)
    (u : CoordinateSpace 3) : CoordinateSpace 3 →L[ℝ] ℝ :=
  k.c 1 • threeSitePC 1 -
    k.alpha 1 • (threeSiteFreeF FT u • threeSitePS 1 + u.1 1 • threeSiteFLinear) +
    k.beta 1 • threeSitePD 1 -
    k.a 2 • (threeSiteFreeE ET u • threeSitePS 1 + u.1 1 • threeSiteELinear) +
    k.b 2 • threeSitePC 2 + k.gamma 2 • threeSitePD 2

def threeSiteRowS3 (FT : ℝ) (k : Rates 3)
    (u : CoordinateSpace 3) : CoordinateSpace 3 →L[ℝ] ℝ :=
  k.c 2 • threeSitePC 2 -
    k.alpha 2 • (threeSiteFreeF FT u • threeSitePS 2 + u.1 2 • threeSiteFLinear) +
    k.beta 2 • threeSitePD 2

def threeSiteRowC0 (ET ST : ℝ) (k : Rates 3)
    (u : CoordinateSpace 3) : CoordinateSpace 3 →L[ℝ] ℝ :=
  k.a 0 • (threeSiteFreeE ET u • threeSiteS0Linear +
    threeSiteFreeS0 ST u • threeSiteELinear) -
    (k.b 0 + k.c 0) • threeSitePC 0

def threeSiteRowC1 (ET : ℝ) (k : Rates 3)
    (u : CoordinateSpace 3) : CoordinateSpace 3 →L[ℝ] ℝ :=
  k.a 1 • (threeSiteFreeE ET u • threeSitePS 0 + u.1 0 • threeSiteELinear) -
    (k.b 1 + k.c 1) • threeSitePC 1

def threeSiteRowC2 (ET : ℝ) (k : Rates 3)
    (u : CoordinateSpace 3) : CoordinateSpace 3 →L[ℝ] ℝ :=
  k.a 2 • (threeSiteFreeE ET u • threeSitePS 1 + u.1 1 • threeSiteELinear) -
    (k.b 2 + k.c 2) • threeSitePC 2

def threeSiteRowD0 (FT : ℝ) (k : Rates 3)
    (u : CoordinateSpace 3) : CoordinateSpace 3 →L[ℝ] ℝ :=
  k.alpha 0 • (threeSiteFreeF FT u • threeSitePS 0 + u.1 0 • threeSiteFLinear) -
    (k.beta 0 + k.gamma 0) • threeSitePD 0

def threeSiteRowD1 (FT : ℝ) (k : Rates 3)
    (u : CoordinateSpace 3) : CoordinateSpace 3 →L[ℝ] ℝ :=
  k.alpha 1 • (threeSiteFreeF FT u • threeSitePS 1 + u.1 1 • threeSiteFLinear) -
    (k.beta 1 + k.gamma 1) • threeSitePD 1

def threeSiteRowD2 (FT : ℝ) (k : Rates 3)
    (u : CoordinateSpace 3) : CoordinateSpace 3 →L[ℝ] ℝ :=
  k.alpha 2 • (threeSiteFreeF FT u • threeSitePS 2 + u.1 2 • threeSiteFLinear) -
    (k.beta 2 + k.gamma 2) • threeSitePD 2

def threeSiteJacobianCLM (ET FT ST : ℝ) (k : Rates 3)
    (u : CoordinateSpace 3) : CoordinateSpace 3 →L[ℝ] CoordinateSpace 3 :=
  (ContinuousLinearMap.pi ![threeSiteRowS1 ET FT k u,
    threeSiteRowS2 ET FT k u, threeSiteRowS3 FT k u]).prod
    ((ContinuousLinearMap.pi ![threeSiteRowC0 ET ST k u,
      threeSiteRowC1 ET k u, threeSiteRowC2 ET k u]).prod
      (ContinuousLinearMap.pi ![threeSiteRowD0 FT k u,
        threeSiteRowD1 FT k u, threeSiteRowD2 FT k u]))


end
end PhosphorylationStableCapacity
