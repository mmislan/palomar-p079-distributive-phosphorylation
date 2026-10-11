module
public import proofs.PhosphorylationStableCapacity.RatioResidualConverse

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section
open PhosphorylationSharpness

/-- The free phosphatase along the positive equilibrium profile with
the prescribed phosphatase and substrate totals. -/
def ratioCurveFreePhosphatase {n : ℕ} (k : Rates n)
    (FT ST u : ℝ) : ℝ :=
  FT / (1 + modelRatioSubstrateLevel k FT ST u *
    phosphataseComplexInventory k u)

/-- A literal equilibrium curve: all mass-action equations and the
phosphatase/substrate totals hold for every positive ratio. -/
def ratioEquilibriumCurve {n : ℕ} (k : Rates n)
    (FT ST u : ℝ) : State n :=
  ratioProfileState k u (modelRatioSubstrateLevel k FT ST u)
    (ratioCurveFreePhosphatase k FT ST u)

/-- The kinase total attained by the equilibrium curve. -/
def ratioCurveKinaseTotal {n : ℕ} (k : Rates n)
    (FT ST u : ℝ) : ℝ :=
  ratioCurveFreePhosphatase k FT ST u *
    (u + modelRatioSubstrateLevel k FT ST u *
      kinaseComplexInventory k u)

theorem ratioEquilibriumCurve_positive_equilibrium_and_totals {n : ℕ}
    (hn : 0 < n) (k : Rates n) (hk : k.Positive)
    (FT ST u : ℝ) (hFT : 0 < FT) (hST : 0 < ST)
    (hu : 0 < u) :
    let x := ratioEquilibriumCurve k FT ST u
    x.Positive ∧ Equilibrium k x ∧
      totalF x = FT ∧ totalS x = ST ∧
      totalE x = ratioCurveKinaseTotal k FT ST u ∧
      x.E/x.F = u := by
  let T := freeSubstrateInventory k u
  let B := kinaseComplexInventory k u
  let D := phosphataseComplexInventory k u
  let s := modelRatioSubstrateLevel k FT ST u
  let f := ratioCurveFreePhosphatase k FT ST u
  let x := ratioEquilibriumCurve k FT ST u
  obtain ⟨hs, hsub⟩ :=
    modelRatioSubstrateLevel_pos_and_inventory hn k hk FT ST u hST hu
  have hD : 0 < D := phosphataseComplexInventory_pos k hk hu hn
  have hdenpos : 0 < 1+s*D := by nlinarith [mul_pos hs hD]
  have hden : 1+s*D ≠ 0 := ne_of_gt hdenpos
  have hf : 0 < f := div_pos hFT hdenpos
  have hFtotal : f*(1+s*D) = FT := by
    change FT/(1+s*D)*(1+s*D) = FT
    exact div_mul_cancel₀ FT hden
  have hStotal : s*T+f*s*(B+D) = ST := by
    calc
      s*T+f*s*(B+D) = ratioSubstrateInventory FT T (B+D) D s := by
        dsimp [f, ratioCurveFreePhosphatase, ratioSubstrateInventory]
        ring
      _ = ST := hsub
  obtain ⟨htE, htF, htS⟩ :=
    ratioProfileState_totals k hk u s f hu hs hf
  change x.Positive ∧ Equilibrium k x ∧
    totalF x = FT ∧ totalS x = ST ∧
    totalE x = ratioCurveKinaseTotal k FT ST u ∧
    x.E/x.F = u
  refine ⟨ratioProfileState_positive k hk u s f hu hs hf,
    ratioProfileState_equilibrium k hk u s f,
    htF.trans hFtotal, htS.trans hStotal, ?_, ?_⟩
  · change totalE (ratioProfileState k u s f) = f * (u + s * B)
    exact htE
  · dsimp [x, ratioEquilibriumCurve, ratioProfileState]
    exact mul_div_cancel_right₀ u (ne_of_gt hf)

/-- On the positive equilibrium curve, the scalar residual is the
remaining kinase-total error multiplied by a positive denominator. -/
theorem ratioEnzymeResidual_eq_curve_total_gap {n : ℕ}
    (hn : 0 < n) (k : Rates n) (hk : k.Positive)
    (ET FT ST u : ℝ) (hST : 0 < ST)
    (hu : 0 < u) :
    ratioEnzymeResidual k ET FT ST u =
      (1 + modelRatioSubstrateLevel k FT ST u *
        phosphataseComplexInventory k u) *
      (ratioCurveKinaseTotal k FT ST u - ET) := by
  let s := modelRatioSubstrateLevel k FT ST u
  let D := phosphataseComplexInventory k u
  have hs :=
    (modelRatioSubstrateLevel_pos_and_inventory
      hn k hk FT ST u hST hu).1
  have hD : 0 < D := phosphataseComplexInventory_pos k hk hu hn
  have hden : 1+s*D ≠ 0 := ne_of_gt (by nlinarith [mul_pos hs hD])
  have hprod : (1+s*D)*(FT/(1+s*D)) = FT := by
    rw [mul_comm]
    exact div_mul_cancel₀ FT hden
  change FT*(u+s*kinaseComplexInventory k u)-ET*(1+s*D) =
    (1+s*D)*
      (FT/(1+s*D)*(u+s*kinaseComplexInventory k u)-ET)
  symm
  calc
    _ = ((1+s*D)*(FT/(1+s*D)))*
        (u+s*kinaseComplexInventory k u)-ET*(1+s*D) := by ring
    _ = FT*(u+s*kinaseComplexInventory k u)-ET*(1+s*D) := by rw [hprod]

end
end PhosphorylationStableCapacity
