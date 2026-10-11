module
public import proofs.PhosphorylationStableCapacity.FiniteFixedRationalLookupDataM3
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.NormNum

@[expose] public section

namespace PhosphorylationStableCapacity
noncomputable section
open PhosphorylationSharpness Polynomial
set_option maxHeartbeats 2000000
set_option maxRecDepth 8192

theorem finiteFixedLookupM3_valid : finiteFixedLookupM3.Valid := by
  let q := finiteFixedLookupM3
  let p : ℝ[X] := arbitrarySplitRawD 3 (finiteFixedOffset 3) (finiteFixedRadius 3) (finiteFixedSpacing 3)
  have hd (i : Fin 4) : (q.release i : ℝ) = p.coeff i := by
    dsimp only [p]
    rw [finiteFixedFourSite_coefficients_exact.1 i]
    fin_cases i <;> norm_num [q, finiteFixedLookupM3, finiteFixedFourSite_DCoefficients]
  have hb (i : Fin 4) : (q.binding i : ℝ) = (arbitrarySplitRawB 3 (finiteFixedOffset 3) (finiteFixedRadius 3) (finiteFixedSpacing 3)).coeff i := by
    rw [finiteFixedFourSite_coefficients_exact.2.1 i]
    fin_cases i <;> norm_num [q, finiteFixedLookupM3, finiteFixedFourSite_BCoefficients]
  have htail : ∀ k : ℕ, 3 < k → p.coeff k = 0 :=
    finiteFixedFourSite_coefficients_positive.1.2
  have hd0 : p.coeff 0 = (q.release (0 : Fin 4) : ℝ) := (hd 0).symm
  have hd1 : p.coeff 1 = (q.release (1 : Fin 4) : ℝ) := (hd 1).symm
  have hd2 : p.coeff 2 = (q.release (2 : Fin 4) : ℝ) := (hd 2).symm
  have hd3 : p.coeff 3 = (q.release (3 : Fin 4) : ℝ) := (hd 3).symm
  have hdLast : p.coeff 4 = 0 := htail 4 (by omega)
  refine ⟨?_, ?_, hb, hd, htail, ?_⟩
  · norm_num [q, finiteFixedLookupM3, finiteFixedSpacing]
  · apply FixedRationalLookup.inventory_cast_of_coeff q p
    · rw [hd0]; norm_num [q, finiteFixedLookupM3]
    · intro i
      fin_cases i <;> norm_num [q, finiteFixedLookupM3, hd0, hd1, hd2, hd3, hdLast]
  · apply FixedRationalLookup.coalescedCoordinate_cast q
    intro i
    rw [finiteFixedFourSite_coalesced_D_exact.1 i]
    fin_cases i <;> norm_num [q, finiteFixedLookupM3, finiteFixedFourSite_coalescedDCoefficients]

end
end PhosphorylationStableCapacity
