module
public import proofs.PhosphorylationStableCapacity.FiniteFixedPrintedFamily
public import proofs.PhosphorylationStableCapacity.ArbitrarySplitConversion

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section
open PhosphorylationSharpness Polynomial

/-- Every one of the six printed finite families places all its prescribed
roots strictly above the physical threshold one. -/
theorem finiteFixed_root_gt_one_of_range (m : ℕ)
    (hm : 1 ≤ m) (hm6 : m ≤ 6) (j : ℕ) :
    1 < offsetSplitRoot (finiteFixedOffset m)
      (finiteFixedSpacing m) j := by
  have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  interval_cases m <;>
    norm_num [offsetSplitRoot, finiteFixedOffset,
      finiteFixedSpacing] at * <;>
    nlinarith

/-- The generic recurrence supplies all degree bounds. For a printed fixed
family, only its finitely many coefficients at indices `0, ..., m` need exact
rational positivity certificates. -/
theorem finiteFixed_raw_dense_of_coeff_positive
    (m : ℕ)
    (hroot : ∀ j, j ≤ 2 * m →
      1 < offsetSplitRoot (finiteFixedOffset m) (finiteFixedSpacing m) j)
    (hD : ∀ i : Fin (m + 1),
      0 < (arbitrarySplitRawD m (finiteFixedOffset m)
        (finiteFixedRadius m) (finiteFixedSpacing m)).coeff i)
    (hB : ∀ i : Fin (m + 1),
      0 < (arbitrarySplitRawB m (finiteFixedOffset m)
        (finiteFixedRadius m) (finiteFixedSpacing m)).coeff i) :
    DensePositive
      (arbitrarySplitRawD m (finiteFixedOffset m)
        (finiteFixedRadius m) (finiteFixedSpacing m)) m ∧
    DensePositive
      (arbitrarySplitRawB m (finiteFixedOffset m)
        (finiteFixedRadius m) (finiteFixedSpacing m)) m := by
  let p := (arbitrarySplitPair m (finiteFixedOffset m)
    (finiteFixedSpacing m)).1
  let q := (arbitrarySplitPair m (finiteFixedOffset m)
    (finiteFixedSpacing m)).2
  have hpq : DensePositive p m ∧ DensePositive q m :=
    arbitrarySplitPair_dense m (finiteFixedOffset m)
      (finiteFixedSpacing m) hroot
  constructor
  · constructor
    · intro i hi
      exact hD ⟨i, by omega⟩
    · intro i hi
      exact (raw_support hpq.1 hpq.2 (finiteFixedRadius m) i hi).1
  · constructor
    · intro i hi
      exact hB ⟨i, by omega⟩
    · intro i hi
      exact (raw_support hpq.1 hpq.2 (finiteFixedRadius m) i hi).2

end
end PhosphorylationStableCapacity
