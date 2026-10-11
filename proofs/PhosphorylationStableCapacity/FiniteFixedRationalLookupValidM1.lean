module
public import proofs.PhosphorylationStableCapacity.FiniteFixedRationalLookupDataM1
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.NormNum

@[expose] public section

namespace PhosphorylationStableCapacity
noncomputable section
open PhosphorylationSharpness Polynomial
set_option maxHeartbeats 2000000
set_option maxRecDepth 8192

theorem finiteFixedLookupM1_valid : finiteFixedLookupM1.Valid := by
  let q := finiteFixedLookupM1
  let p : ℝ[X] := arbitrarySplitRawD 1 (finiteFixedOffset 1) (finiteFixedRadius 1) (finiteFixedSpacing 1)
  have hd (i : Fin 2) : (q.release i : ℝ) = p.coeff i := by
    dsimp only [p]
    rw [finiteFixedTwoSite_coefficients_exact.1 i]
    fin_cases i <;> norm_num [q, finiteFixedLookupM1, finiteFixedTwoSite_DCoefficients]
  have hb (i : Fin 2) : (q.binding i : ℝ) = (arbitrarySplitRawB 1 (finiteFixedOffset 1) (finiteFixedRadius 1) (finiteFixedSpacing 1)).coeff i := by
    rw [finiteFixedTwoSite_coefficients_exact.2.1 i]
    fin_cases i <;> norm_num [q, finiteFixedLookupM1, finiteFixedTwoSite_BCoefficients]
  have htail : ∀ k : ℕ, 1 < k → p.coeff k = 0 :=
    finiteFixedTwoSite_coefficients_positive.1.2
  have hd0 : p.coeff 0 = (q.release (0 : Fin 2) : ℝ) := (hd 0).symm
  have hd1 : p.coeff 1 = (q.release (1 : Fin 2) : ℝ) := (hd 1).symm
  have hdLast : p.coeff 2 = 0 := htail 2 (by omega)
  refine ⟨?_, ?_, hb, hd, htail, ?_⟩
  · norm_num [q, finiteFixedLookupM1, finiteFixedSpacing]
  · apply FixedRationalLookup.inventory_cast_of_coeff q p
    · rw [hd0]; norm_num [q, finiteFixedLookupM1]
    · intro i
      fin_cases i <;> norm_num [q, finiteFixedLookupM1, hd0, hd1, hdLast]
  · apply FixedRationalLookup.coalescedCoordinate_cast q
    intro i
    rw [finiteFixedTwoSite_coalesced_D_exact.1 i]
    fin_cases i <;> norm_num [q, finiteFixedLookupM1, finiteFixedTwoSite_coalescedDCoefficients]

end
end PhosphorylationStableCapacity
