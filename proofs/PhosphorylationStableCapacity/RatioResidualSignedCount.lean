module
public import proofs.PhosphorylationStableCapacity.ScalarCrossingCount
public import proofs.PhosphorylationStableCapacity.PositiveEquilibriumExistence

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section
open PhosphorylationSharpness

/-- The simple positive roots of the literal scalar residual have signed
crossing count one. -/
theorem ratio_residual_signed_crossing_one {n : ℕ}
    (hn : 0 < n) (k : Rates n) (hk : k.Positive)
    (ET FT ST : ℝ) (hET : 0 < ET)
    (hFT : 0 < FT) (hST : 0 < ST)
    (hfinite : {u : ℝ | 0 < u ∧
      ratioEnzymeResidual k ET FT ST u = 0}.Finite)
    (hsimple : ∀ u : ℝ, 0 < u →
      ratioEnzymeResidual k ET FT ST u = 0 →
      deriv (ratioEnzymeResidual k ET FT ST) u ≠ 0) :
    ∑ u ∈ hfinite.toFinset,
      crossingCharge (ratioEnzymeResidual k ET FT ST) u = 1 := by
  let f := ratioEnzymeResidual k ET FT ST
  obtain ⟨δ, hδ, hsmall⟩ :=
    ratioEnzymeResidual_negative_near_zero
      hn k hk ET FT ST hET hFT hST
  obtain ⟨R, hR, hlarge⟩ :=
    ratioEnzymeResidual_positive_for_large_ratio
      hn k hk ET FT ST hET hFT hST
  let a := min (δ/2) (R/2)
  let b := R+1
  have ha : 0 < a := lt_min (by positivity) (by positivity)
  have haδ : a < δ := lt_of_le_of_lt (min_le_left ..) (by linarith)
  have hab : a < b := by
    have h := min_le_right (δ/2) (R/2)
    dsimp [a, b]
    linarith
  have hRb : R < b := by dsimp [b]; linarith
  have hneg : f a < 0 := hsmall a ha haδ
  have hpos : 0 < f b := hlarge b hRb
  have hcont : ContinuousOn f (Set.Icc a b) := by
    intro u hu
    have hu' : 0 < u := lt_of_lt_of_le ha hu.1
    exact (ratioEnzymeResidual_differentiableAt
      hn k hk ET FT ST u hST hu').continuousAt.continuousWithinAt
  have hset : {u : ℝ | a < u ∧ u < b ∧ f u = 0} =
      {u : ℝ | 0 < u ∧ f u = 0} := by
    ext u
    constructor
    · rintro ⟨hau, _, hzero⟩
      exact ⟨lt_trans ha hau, hzero⟩
    · rintro ⟨hu, hzero⟩
      have hau : a < u := by
        by_contra h
        have hual : u ≤ a := le_of_not_gt h
        have huδ : u < δ := lt_of_le_of_lt hual haδ
        have := hsmall u hu huδ
        linarith
      have hub : u < b := by
        by_contra h
        have hbu : b ≤ u := le_of_not_gt h
        have hRu : R < u := lt_of_lt_of_le hRb hbu
        have := hlarge u hRu
        linarith
      exact ⟨hau, hub, hzero⟩
  have hfinite' : {u : ℝ | a < u ∧ u < b ∧ f u = 0}.Finite := by
    rw [hset]
    exact hfinite
  have hsimple' : ∀ u : ℝ, a < u → u < b → f u = 0 →
      deriv f u ≠ 0 := by
    intro u hau _ hzero
    exact hsimple u (lt_trans ha hau) hzero
  have hcount := finite_simple_roots_signed_crossing_one
    f a b hab hcont hneg hpos hfinite' hsimple'
  simpa only [hset] using hcount

end
end PhosphorylationStableCapacity
