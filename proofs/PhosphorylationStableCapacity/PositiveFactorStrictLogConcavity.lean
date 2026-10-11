module
public import proofs.PhosphorylationStableCapacity.PositiveLinearStrictLogConcavityStep

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section

/-- Products of positive linear factors have strictly log-concave
coefficients at every interior index. -/
theorem positiveFactorProduct_strictLogConcave (rs : List ℝ)
    (hrs : ∀ r ∈ rs, 0 < r) :
    CoeffStrictLogConcave (positiveFactorProduct rs) rs.length := by
  induction rs with
  | nil =>
      intro i hi0 him
      simp at him
  | cons r rs ih =>
      have hr : 0 < r := hrs r (by simp)
      have hrs' : ∀ s ∈ rs, 0 < s := by
        intro s hs
        exact hrs s (by simp [hs])
      simpa [positiveFactorProduct] using
        positiveLinearStep_strictLogConcave
          (positiveFactorProduct_dense rs hrs')
          (positiveFactorProduct_logconcave rs hrs')
          (ih hrs') hr

end
end PhosphorylationStableCapacity
