module
public import proofs.PhosphorylationStableCapacity.PaperFixedBindingChallengeConstruction435
public import proofs.PhosphorylationStableCapacity.ArbitrarySplitGlobalBPositive435
public import proofs.PhosphorylationStableCapacity.ReadoutGlobalMonotonicity435

@[expose] public section

namespace PhosphorylationStableCapacity
noncomputable section
open PhosphorylationSharpness Polynomial
open scoped BigOperators

def PaperCoefficientDense (p : ℝ[X]) (m : ℕ) : Prop := (∀ i ≤ m, 0 < p.coeff i) ∧ ∀ i, m < i → p.coeff i = 0

theorem paper_global_conversion_quotient_and_D_positive (m : ℕ) (ξ : ℕ → ℝ) (δ r : ℝ) (hr : 0 < r) (hroot : ∀ j, j ≤ 2*m → 1 < paperOffsetRoot ξ δ j) : PaperCoefficientDense (paperQuotient (paperSplitPair m ξ δ).1 (paperSplitPair m ξ δ).2 r) m ∧ PaperCoefficientDense (paperSplitD m ξ r δ) m := by
  constructor
  · simpa only [PaperCoefficientDense, PhosphorylationSharpness.DensePositive, paperQuotient, PhosphorylationSharpness.quotient, PhosphorylationSharpness.conversionNumerator, paperSplitPair_eq_arbitrarySplitPair] using
      arbitrarySplit_quotient_dense_every_positive_source m ξ δ r hr hroot
  · rw [paperSplitD_eq_arbitrarySplitRawD]
    exact arbitrarySplitRawD_dense_every_positive_source m ξ δ r hr hroot

theorem paper_global_conversion_B_positive (m : ℕ) (ξ : ℕ → ℝ) (δ r : ℝ) (hr : 0 < r) (hroot : ∀ j, j ≤ 2*m → 1 < paperOffsetRoot ξ δ j) (hfar : ∀ j, j ≤ 2*m → paperOffsetRoot ξ δ j < Real.sqrt (1+8*r)) (hsum : (∑ j ∈ Finset.range (2*m+1), paperOffsetRoot ξ δ j) ≤ 4*r+Real.sqrt (1+8*r)) : PaperCoefficientDense (paperSplitB m ξ r δ) m := by
  rw [paperSplitB_eq_arbitrarySplitRawB]
  exact arbitrarySplitRawB_dense_of_global_paper_bounds m ξ δ r hr hroot hfar hsum

theorem paper_global_readout_strict_order (m : ℕ) (D : ℝ[X]) (hD : PaperCoefficientDense D m) : StrictMonoOn (fun x : ℝ => (D.coeff m/2)*((paperRatio x)^m/D.eval (paperRatio x))*((x-1)*(x+5)/(x+1))) (Set.Ioi 1) := by
  exact splitReadoutScalar_strictMonoOn_Ioi_one m D hD

end
end PhosphorylationStableCapacity
