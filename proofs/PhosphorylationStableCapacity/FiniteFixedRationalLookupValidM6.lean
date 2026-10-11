module
public import proofs.PhosphorylationStableCapacity.FiniteFixedRationalLookupDataM6
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.NormNum

@[expose] public section

namespace PhosphorylationStableCapacity
noncomputable section
open PhosphorylationSharpness Polynomial
set_option maxHeartbeats 2000000
set_option maxRecDepth 8192

theorem finiteFixedLookupM6_valid : finiteFixedLookupM6.Valid := by
  let q := finiteFixedLookupM6
  let p : ℝ[X] := arbitrarySplitRawD 6 (finiteFixedOffset 6) (finiteFixedRadius 6) (finiteFixedSpacing 6)
  have hd (i : Fin 7) : (q.release i : ℝ) = p.coeff i := by
    dsimp only [p]
    rw [finiteFixedSevenSite_coefficients_exact.1 i]
    fin_cases i <;> norm_num [q, finiteFixedLookupM6, finiteFixedSevenSite_DCoefficients]
  have hb (i : Fin 7) : (q.binding i : ℝ) = (arbitrarySplitRawB 6 (finiteFixedOffset 6) (finiteFixedRadius 6) (finiteFixedSpacing 6)).coeff i := by
    rw [finiteFixedSevenSite_coefficients_exact.2.1 i]
    fin_cases i <;> norm_num [q, finiteFixedLookupM6, finiteFixedSevenSite_BCoefficients]
  have htail : ∀ k : ℕ, 6 < k → p.coeff k = 0 :=
    finiteFixedSevenSite_coefficients_positive.1.2
  have hd0 : p.coeff 0 = (q.release (0 : Fin 7) : ℝ) := (hd 0).symm
  have hd1 : p.coeff 1 = (q.release (1 : Fin 7) : ℝ) := (hd 1).symm
  have hd2 : p.coeff 2 = (q.release (2 : Fin 7) : ℝ) := (hd 2).symm
  have hd3 : p.coeff 3 = (q.release (3 : Fin 7) : ℝ) := (hd 3).symm
  have hd4 : p.coeff 4 = (q.release (4 : Fin 7) : ℝ) := (hd 4).symm
  have hd5 : p.coeff 5 = (q.release (5 : Fin 7) : ℝ) := (hd 5).symm
  have hd6 : p.coeff 6 = (q.release (6 : Fin 7) : ℝ) := (hd 6).symm
  have hdLast : p.coeff 7 = 0 := htail 7 (by omega)
  refine ⟨?_, ?_, hb, hd, htail, ?_⟩
  · norm_num [q, finiteFixedLookupM6, finiteFixedSpacing]
  · apply FixedRationalLookup.inventory_cast_of_coeff q p
    · rw [hd0]; norm_num [q, finiteFixedLookupM6]
    · intro i
      fin_cases i <;> norm_num [q, finiteFixedLookupM6, hd0, hd1, hd2, hd3, hd4, hd5, hd6, hdLast]
  · apply FixedRationalLookup.coalescedCoordinate_cast q
    intro i
    rw [finiteFixedSevenSite_coalesced_D_exact.1 i]
    fin_cases i <;> norm_num [q, finiteFixedLookupM6, finiteFixedSevenSite_coalescedDCoefficients]

end
end PhosphorylationStableCapacity
