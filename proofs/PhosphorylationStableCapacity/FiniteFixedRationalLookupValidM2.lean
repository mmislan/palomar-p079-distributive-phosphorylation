module
public import proofs.PhosphorylationStableCapacity.FiniteFixedRationalLookupDataM2
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.NormNum

@[expose] public section

namespace PhosphorylationStableCapacity
noncomputable section
open PhosphorylationSharpness Polynomial
set_option maxHeartbeats 2000000
set_option maxRecDepth 8192

theorem finiteFixedLookupM2_valid : finiteFixedLookupM2.Valid := by
  let q := finiteFixedLookupM2
  let p : ℝ[X] := arbitrarySplitRawD 2 (finiteFixedOffset 2) (finiteFixedRadius 2) (finiteFixedSpacing 2)
  have hd (i : Fin 3) : (q.release i : ℝ) = p.coeff i := by
    dsimp only [p]
    rw [finiteFixedThreeSite_coefficients_exact.1 i]
    fin_cases i <;> norm_num [q, finiteFixedLookupM2, finiteFixedThreeSite_DCoefficients]
  have hb (i : Fin 3) : (q.binding i : ℝ) = (arbitrarySplitRawB 2 (finiteFixedOffset 2) (finiteFixedRadius 2) (finiteFixedSpacing 2)).coeff i := by
    rw [finiteFixedThreeSite_coefficients_exact.2.1 i]
    fin_cases i <;> norm_num [q, finiteFixedLookupM2, finiteFixedThreeSite_BCoefficients]
  have htail : ∀ k : ℕ, 2 < k → p.coeff k = 0 :=
    finiteFixedThreeSite_coefficients_positive.1.2
  have hd0 : p.coeff 0 = (q.release (0 : Fin 3) : ℝ) := (hd 0).symm
  have hd1 : p.coeff 1 = (q.release (1 : Fin 3) : ℝ) := (hd 1).symm
  have hd2 : p.coeff 2 = (q.release (2 : Fin 3) : ℝ) := (hd 2).symm
  have hdLast : p.coeff 3 = 0 := htail 3 (by omega)
  refine ⟨?_, ?_, hb, hd, htail, ?_⟩
  · norm_num [q, finiteFixedLookupM2, finiteFixedSpacing]
  · apply FixedRationalLookup.inventory_cast_of_coeff q p
    · rw [hd0]; norm_num [q, finiteFixedLookupM2]
    · intro i
      fin_cases i <;> norm_num [q, finiteFixedLookupM2, hd0, hd1, hd2, hdLast]
  · apply FixedRationalLookup.coalescedCoordinate_cast q
    intro i
    rw [finiteFixedThreeSite_coalesced_D_exact.1 i]
    fin_cases i <;> norm_num [q, finiteFixedLookupM2, finiteFixedThreeSite_coalescedDCoefficients]

end
end PhosphorylationStableCapacity
