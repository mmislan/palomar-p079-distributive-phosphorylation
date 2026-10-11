module
public import proofs.PhosphorylationStableCapacity.PositiveLinearLogConcavityStep

@[expose] public section

namespace PhosphorylationStableCapacity

open Polynomial PhosphorylationSharpness

noncomputable section

def positiveFactorProduct : List ℝ → ℝ[X]
  | [] => 1
  | r :: rs => positiveLinearStep r (positiveFactorProduct rs)

theorem positiveFactorProduct_dense (rs : List ℝ)
    (hrs : ∀ r ∈ rs, 0 < r) :
    DensePositive (positiveFactorProduct rs) rs.length := by
  induction rs with
  | nil =>
      simpa [positiveFactorProduct] using dense_constant 1 (by norm_num)
  | cons r rs ih =>
      have hr : 0 < r := hrs r (by simp)
      have hrs' : ∀ s ∈ rs, 0 < s := by
        intro s hs
        exact hrs s (by simp [hs])
      simpa [positiveFactorProduct] using
        positiveLinearStep_dense (ih hrs') hr

/-- Every finite product of positive linear factors has a positive,
log-concave coefficient sequence on its full support. -/
theorem positiveFactorProduct_logconcave (rs : List ℝ)
    (hrs : ∀ r ∈ rs, 0 < r) :
    CoeffLogConcave (positiveFactorProduct rs) rs.length := by
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
        positiveLinearStep_logconcave
          (positiveFactorProduct_dense rs hrs') (ih hrs') hr

end
end PhosphorylationStableCapacity
