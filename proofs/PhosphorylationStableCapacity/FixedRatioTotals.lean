module
public import proofs.PhosphorylationStableCapacity.GeneralEquilibriumRatios

@[expose] public section
set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

namespace PhosphorylationStableCapacity

noncomputable section

/-- At a fixed free-enzyme ratio, the phosphatase total determines
free phosphatase as `FT / (1 + D*s)`. The substrate total then has
this scalar form, where `s` is the level-zero substrate. -/
private def fixedRatioSubstrateTotal
    (FT T K D s : ℝ) : ℝ :=
  s*T + (FT*K)*(s/(1+D*s))

private theorem fixedRatioFraction_strict
    (D s₁ s₂ : ℝ)
    (hD : 0 ≤ D) (hs₁ : 0 ≤ s₁) (hs₂ : 0 ≤ s₂)
    (hlt : s₁ < s₂) :
    s₁/(1+D*s₁) < s₂/(1+D*s₂) := by
  have hden₁ : 0 < 1+D*s₁ := by
    nlinarith [mul_nonneg hD hs₁]
  have hden₂ : 0 < 1+D*s₂ := by
    nlinarith [mul_nonneg hD hs₂]
  apply (div_lt_div_iff₀ hden₁ hden₂).2
  nlinarith

/-- The scalar substrate inventory is strictly increasing in the
level-zero substrate, for positive model coefficients. -/
theorem fixedRatioSubstrateTotal_strict
    (FT T K D s₁ s₂ : ℝ)
    (hFT : 0 < FT) (hT : 0 < T) (hK : 0 < K)
    (hD : 0 ≤ D) (hs₁ : 0 ≤ s₁) (hs₂ : 0 ≤ s₂)
    (hlt : s₁ < s₂) :
    fixedRatioSubstrateTotal FT T K D s₁ <
      fixedRatioSubstrateTotal FT T K D s₂ := by
  dsimp [fixedRatioSubstrateTotal]
  exact add_lt_add
    (mul_lt_mul_of_pos_right hlt hT)
    (mul_lt_mul_of_pos_left
      (fixedRatioFraction_strict D s₁ s₂ hD hs₁ hs₂ hlt)
      (mul_pos hFT hK))

/-- Two positive solutions of the fixed-ratio inventory equations
with the same phosphatase and substrate totals coincide. This lemma
will supply the exceptional-case injection in the universal count. -/
theorem fixedRatioTotals_unique
    (FT ST T K D s₁ s₂ f₁ f₂ : ℝ)
    (hFT : 0 < FT) (hT : 0 < T) (hK : 0 < K)
    (hD : 0 ≤ D) (hs₁ : 0 < s₁) (hs₂ : 0 < s₂)
    (hF₁ : FT = f₁*(1+D*s₁))
    (hF₂ : FT = f₂*(1+D*s₂))
    (hS₁ : ST = s₁*T + f₁*s₁*K)
    (hS₂ : ST = s₂*T + f₂*s₂*K) :
    s₁ = s₂ ∧ f₁ = f₂ := by
  have hden₁ : 1+D*s₁ ≠ 0 := ne_of_gt (by
    nlinarith [mul_nonneg hD hs₁.le])
  have hden₂ : 1+D*s₂ ≠ 0 := ne_of_gt (by
    nlinarith [mul_nonneg hD hs₂.le])
  have hfexpr₁ : f₁ = FT/(1+D*s₁) := by
    apply (eq_div_iff hden₁).2
    linarith [hF₁]
  have hfexpr₂ : f₂ = FT/(1+D*s₂) := by
    apply (eq_div_iff hden₂).2
    linarith [hF₂]
  have hvalue₁ : ST = fixedRatioSubstrateTotal FT T K D s₁ := by
    rw [hS₁, hfexpr₁]
    dsimp [fixedRatioSubstrateTotal]
    ring
  have hvalue₂ : ST = fixedRatioSubstrateTotal FT T K D s₂ := by
    rw [hS₂, hfexpr₂]
    dsimp [fixedRatioSubstrateTotal]
    ring
  have hs : s₁ = s₂ := by
    rcases lt_trichotomy s₁ s₂ with hlt | heq | hgt
    · have hstrict := fixedRatioSubstrateTotal_strict
        FT T K D s₁ s₂ hFT hT hK hD hs₁.le hs₂.le hlt
      rw [← hvalue₁, ← hvalue₂] at hstrict
      exact False.elim (lt_irrefl ST hstrict)
    · exact heq
    · have hstrict := fixedRatioSubstrateTotal_strict
        FT T K D s₂ s₁ hFT hT hK hD hs₂.le hs₁.le hgt
      rw [← hvalue₁, ← hvalue₂] at hstrict
      exact False.elim (lt_irrefl ST hstrict)
  refine ⟨hs, ?_⟩
  rw [hs] at hfexpr₁
  exact hfexpr₁.trans hfexpr₂.symm

end
end PhosphorylationStableCapacity
