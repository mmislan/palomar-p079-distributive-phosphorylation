module
public import proofs.PhosphorylationStableCapacity.FiniteFixedRationalLookupDataM4
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.NormNum

@[expose] public section

namespace PhosphorylationStableCapacity
noncomputable section
open PhosphorylationSharpness Polynomial
set_option maxHeartbeats 2000000
set_option maxRecDepth 8192

theorem finiteFixedLookupM4_valid : finiteFixedLookupM4.Valid := by
  let q := finiteFixedLookupM4
  let p : ℝ[X] := arbitrarySplitRawD 4 (finiteFixedOffset 4) (finiteFixedRadius 4) (finiteFixedSpacing 4)
  have hd (i : Fin 5) : (q.release i : ℝ) = p.coeff i := by
    dsimp only [p]
    rw [finiteFixedFiveSite_coefficients_exact.1 i]
    fin_cases i <;> norm_num [q, finiteFixedLookupM4, finiteFixedFiveSite_DCoefficients]
  have hb (i : Fin 5) : (q.binding i : ℝ) = (arbitrarySplitRawB 4 (finiteFixedOffset 4) (finiteFixedRadius 4) (finiteFixedSpacing 4)).coeff i := by
    rw [finiteFixedFiveSite_coefficients_exact.2.1 i]
    fin_cases i <;> norm_num [q, finiteFixedLookupM4, finiteFixedFiveSite_BCoefficients]
  have htail : ∀ k : ℕ, 4 < k → p.coeff k = 0 :=
    finiteFixedFiveSite_coefficients_positive.1.2
  have hd0 : p.coeff 0 = (q.release (0 : Fin 5) : ℝ) := (hd 0).symm
  have hd1 : p.coeff 1 = (q.release (1 : Fin 5) : ℝ) := (hd 1).symm
  have hd2 : p.coeff 2 = (q.release (2 : Fin 5) : ℝ) := (hd 2).symm
  have hd3 : p.coeff 3 = (q.release (3 : Fin 5) : ℝ) := (hd 3).symm
  have hd4 : p.coeff 4 = (q.release (4 : Fin 5) : ℝ) := (hd 4).symm
  have hdLast : p.coeff 5 = 0 := htail 5 (by omega)
  refine ⟨?_, ?_, hb, hd, htail, ?_⟩
  · norm_num [q, finiteFixedLookupM4, finiteFixedSpacing]
  · apply FixedRationalLookup.inventory_cast_of_coeff q p
    · rw [hd0]; norm_num [q, finiteFixedLookupM4]
    · intro i
      fin_cases i <;> norm_num [q, finiteFixedLookupM4, hd0, hd1, hd2, hd3, hd4, hdLast]
  · apply FixedRationalLookup.coalescedCoordinate_cast q
    intro i
    rw [finiteFixedFiveSite_coalesced_D_exact.1 i]
    fin_cases i <;> norm_num [q, finiteFixedLookupM4, finiteFixedFiveSite_coalescedDCoefficients]

end
end PhosphorylationStableCapacity
