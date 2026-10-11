module
public import proofs.PhosphorylationStableCapacity.ArbitrarySplitInterlacingTail435
public import proofs.PhosphorylationStableCapacity.PaperFixedBindingChallengeConstruction435

@[expose] public section

namespace PhosphorylationStableCapacity
noncomputable section
open Polynomial PhosphorylationSharpness
open scoped BigOperators

/-- Literal independent paper endpoint: complete simple negative interlacing,
both positive-residue expansions, and both coefficient-ratio conclusions. -/
theorem paper_global_interlacing_partial_fractions_and_ratios (m : ℕ) (ξ : ℕ → ℝ) (δ : ℝ) (hroot : ∀ j, j ≤ 2*m → 1 < paperOffsetRoot ξ δ j) : let p := (paperSplitPair m ξ δ).1; let q := (paperSplitPair m ξ δ).2; ∃ ν ζ σ τ : Fin m → ℝ, StrictAnti ν ∧ StrictAnti ζ ∧ (∀ i, ν i < ζ i ∧ ζ i < 0 ∧ 0 < σ i ∧ 0 < τ i ∧ p.eval (ν i) = 0 ∧ q.eval (ζ i) = 0 ∧ p.derivative.eval (ν i) ≠ 0 ∧ q.derivative.eval (ζ i) ≠ 0 ∧ σ i = p.eval (ζ i)/q.derivative.eval (ζ i) ∧ τ i = -q.eval (ν i)/p.derivative.eval (ν i)) ∧ (∀ i j, i < j → ζ j < ν i) ∧ p = C (p.coeff m)*(∏ i, (X-C (ν i))) ∧ q = C (q.coeff m)*(∏ i, (X-C (ζ i))) ∧ (∀ u, (∀ i, u ≠ ζ i) → p.eval u/q.eval u = p.coeff m/q.coeff m + ∑ i, σ i/(u-ζ i)) ∧ (∀ u, (∀ i, u ≠ ν i) → q.eval u/p.eval u = q.coeff m/p.coeff m - ∑ i, τ i/(u-ν i)) ∧ StrictMonoOn (fun i : ℕ => (if i = 0 then 0 else q.coeff (i-1))/q.coeff i) (Set.Iic m) ∧ (∀ i < m, q.coeff i/p.coeff i ≤ q.coeff (i+1)/p.coeff (i+1)) := by
  rw [paperSplitPair_eq_arbitrarySplitPair]
  dsimp only
  let h := arbitrarySplit_interlacing_factorization m ξ δ hroot
  have hd := arbitrarySplitPair_dense m ξ δ hroot
  refine ⟨h.numeratorRoots, h.denominatorRoots, h.numeratorResidue, h.denominatorResidue,
    h.numerator_strictAnti, h.denominator_strictAnti, ?_, h.cross_lt, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    exact ⟨h.matched_lt i, h.denominator_neg i, h.numeratorResidue_pos i,
      h.denominatorResidue_pos i, (arbitrarySplitNRoot_spec m ξ δ hroot i).1,
      (arbitrarySplitJRoot_bounds m ξ δ hroot i).2.2,
      h.numerator_root_derivative_ne_zero i, h.denominator_root_derivative_ne_zero i,
      h.numeratorResidue_eq_derivative i, h.denominatorResidue_eq_derivative i⟩
  · simpa only [Polynomial.leadingCoeff, hd.1.degree_eq, Lagrange.nodal] using h.numerator_factorization
  · simpa only [Polynomial.leadingCoeff, hd.2.degree_eq, Lagrange.nodal] using h.denominator_factorization
  · intro u hu
    simpa only [Polynomial.leadingCoeff, hd.1.degree_eq, hd.2.degree_eq] using h.numerator_partial_fractions u hu
  · intro u hu
    simpa only [Polynomial.leadingCoeff, hd.1.degree_eq, hd.2.degree_eq] using h.denominator_partial_fractions u hu
  · exact arbitrarySplitJ_coefficientPreviousRatio_strictMonoOn m ξ δ hroot
  · exact arbitrarySplitJN_coeff_ratio_mono m ξ δ hroot

end
end PhosphorylationStableCapacity
