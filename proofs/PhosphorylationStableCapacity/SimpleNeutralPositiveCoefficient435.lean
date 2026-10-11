module
public import proofs.PhosphorylationStableCapacity.SplitSlowRoot
public import proofs.PhosphorylationStableCapacity.HurwitzPolynomialConstantPositive
public import proofs.PhosphorylationStableCapacity.SaddleSpectrumOpenness435

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section

open Matrix Polynomial

/-- The positive transverse characteristic coefficient follows from the
simple-neutral Hurwitz-complement certificate for any finite real matrix,
including every independently weighted current matrix. -/
theorem simpleNeutral_real_charpoly_coeff_one_pos
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (J : Matrix ι ι ℝ)
    (hspec : SimpleNeutralHurwitzComplement J) :
    0 < J.charpoly.coeff 1 := by
  obtain ⟨q, hfactor, hq0, hleft⟩ := hspec
  have hp0 : J.charpoly.coeff 0 = 0 :=
    simpleNeutral_real_charpoly_coeff_zero J
      ⟨q, hfactor, hq0, hleft⟩
  have hfac : J.charpoly.map (algebraMap ℝ ℂ) = X*q := by
    simpa only [Matrix.charpoly_map] using hfactor
  exact monic_simple_neutral_polynomial_coeff_one_pos
    J.charpoly q (Matrix.charpoly_monic J) hp0 hfac hleft

/-- One strictly positive lower bound for the transverse coefficient
on a compact continuously varying simple-neutral family. -/
theorem compact_simpleNeutral_charpoly_coeff_one_lower
    {α ι : Type*} [TopologicalSpace α]
    [Fintype ι] [DecidableEq ι]
    (K : Set α) (hK : IsCompact K)
    (J : α → Matrix ι ι ℝ) (hJ : ContinuousOn J K)
    (hspec : ∀ a ∈ K, SimpleNeutralHurwitzComplement (J a)) :
    ∃ c : ℝ, 0 < c ∧ ∀ a ∈ K, c ≤ (J a).charpoly.coeff 1 := by
  by_cases hnon : K.Nonempty
  · have hc : ContinuousOn (fun a => (J a).charpoly.coeff 1) K := by
      intro a ha
      exact (continuousAt_matrix_charpoly_coeff (J a) 1).comp_continuousWithinAt
        (hJ a ha)
    obtain ⟨a₀, ha₀, hmin⟩ := hK.exists_isMinOn hnon hc
    exact ⟨(J a₀).charpoly.coeff 1,
      simpleNeutral_real_charpoly_coeff_one_pos (J a₀) (hspec a₀ ha₀),
      fun a ha => hmin ha⟩
  · refine ⟨1, by norm_num, ?_⟩
    intro a ha
    exact (hnon ⟨a, ha⟩).elim

end

end PhosphorylationStableCapacity
