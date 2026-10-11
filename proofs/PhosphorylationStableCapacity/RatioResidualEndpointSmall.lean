module
public import proofs.PhosphorylationStableCapacity.RatioSubstrateBounds

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section
open PhosphorylationSharpness Filter
open scoped Topology

/-- The exact scalar residual is negative at every sufficiently
small positive enzyme ratio. No limit of the explicit quadratic root
at zero is needed: its substrate level is bounded by `ST`. -/
theorem ratioEnzymeResidual_negative_near_zero {n : ℕ}
    (hn : 0 < n) (k : Rates n) (hk : k.Positive)
    (ET FT ST : ℝ) (hET : 0 < ET)
    (hFT : 0 < FT) (hST : 0 < ST) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ u : ℝ, 0 < u → u < δ →
      ratioEnzymeResidual k ET FT ST u < 0 := by
  have hBzero : kinaseComplexInventory k 0 = 0 := by
    simp [kinaseComplexInventory, pow_succ]
  have hcont : ContinuousAt
      (fun u : ℝ => FT*(u+ST*kinaseComplexInventory k u)) 0 := by
    unfold kinaseComplexInventory
    fun_prop
  have hnear : ∀ᶠ u : ℝ in nhds 0,
      FT*(u+ST*kinaseComplexInventory k u) < ET :=
    hcont.eventually (by simpa [hBzero] using eventually_lt_nhds hET)
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp hnear
  refine ⟨δ, hδ, ?_⟩
  intro u hu hult
  have hmem : u ∈ Metric.ball (0 : ℝ) δ := by
    simpa [Metric.mem_ball, Real.dist_eq, abs_of_pos hu] using hult
  have hsmall := hball hmem
  let s := modelRatioSubstrateLevel k FT ST u
  let B := kinaseComplexInventory k u
  let D := phosphataseComplexInventory k u
  have hs : 0 < s :=
    (modelRatioSubstrateLevel_pos_and_inventory
      hn k hk FT ST u hST hu).1
  have hslt : s < ST :=
    modelRatioSubstrateLevel_lt_ST hn k hk FT ST u hFT hST hu
  have hB : 0 < B := kinaseComplexInventory_pos k hk hu hn
  have hD : 0 < D := phosphataseComplexInventory_pos k hk hu hn
  have hmul : s*B < ST*B := mul_lt_mul_of_pos_right hslt hB
  have hFTmul : FT*(s*B) < FT*(ST*B) :=
    mul_lt_mul_of_pos_left hmul hFT
  have hETden : ET ≤ ET*(1+s*D) := by
    nlinarith [mul_pos hs hD]
  change FT*(u+ST*B)<ET at hsmall
  change FT*(u+s*B)-ET*(1+s*D)<0
  linarith

end
end PhosphorylationStableCapacity
