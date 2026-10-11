module
public import proofs.PhosphorylationStableCapacity.FiniteFixedCoefficientRecurrence
public import proofs.PhosphorylationStableCapacity.CoalescedFiniteSource
public import proofs.PhosphorylationStableCapacity.FiniteCoalescedCoefficientBridge
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.NormNum

@[expose] public section

namespace PhosphorylationStableCapacity
noncomputable section
open PhosphorylationSharpness Polynomial
set_option maxHeartbeats 2000000
set_option maxRecDepth 8192

def finiteFixedFourSite_DCoefficients : Fin 4 → ℝ :=
  ![(1637874945 : ℝ) / 64, (90589694571 : ℝ) / 8, (16876166424 : ℝ), (1578163584 : ℝ)]
def finiteFixedFourSite_BCoefficients : Fin 4 → ℝ :=
  ![(1521174206475 : ℝ) / 64, (1771980942105 : ℝ) / 16, (73813328160 : ℝ), (294951360 : ℝ)]

/-- Exact coefficient lookup and positivity for the printed n=4 family. -/
theorem finiteFixedFourSite_coefficients_exact :
    (∀ i : Fin 4, (arbitrarySplitRawD 3 (finiteFixedOffset 3)
      (finiteFixedRadius 3) (finiteFixedSpacing 3)).coeff i = finiteFixedFourSite_DCoefficients i) ∧
    (∀ i : Fin 4, (arbitrarySplitRawB 3 (finiteFixedOffset 3)
      (finiteFixedRadius 3) (finiteFixedSpacing 3)).coeff i = finiteFixedFourSite_BCoefficients i) ∧
    DensePositive
      (arbitrarySplitRawD 3 (finiteFixedOffset 3)
        (finiteFixedRadius 3) (finiteFixedSpacing 3)) 3 ∧
    DensePositive
      (arbitrarySplitRawB 3 (finiteFixedOffset 3)
        (finiteFixedRadius 3) (finiteFixedSpacing 3)) 3 := by
  let p := (arbitrarySplitPair 3 (finiteFixedOffset 3)
    (finiteFixedSpacing 3)).1
  let q := (arbitrarySplitPair 3 (finiteFixedOffset 3)
    (finiteFixedSpacing 3)).2
  let D := arbitrarySplitRawD 3 (finiteFixedOffset 3)
    (finiteFixedRadius 3) (finiteFixedSpacing 3)
  let B := arbitrarySplitRawB 3 (finiteFixedOffset 3)
    (finiteFixedRadius 3) (finiteFixedSpacing 3)
  have hD_eq : D = rawD p q 4 := rfl
  have hp0 : p.coeff 0 = (103635 : ℝ) / 16 := by
    norm_num [p, arbitrarySplitPair, offsetSplitRoot, finiteFixedOffset, finiteFixedSpacing, nextN, nextJ, coeff_add, coeff_C_mul, coeff_X_mul, eval_add, eval_mul, eval_C, eval_X]
  have hp1 : p.coeff 1 = (46353 : ℝ) / 2 := by
    norm_num [p, arbitrarySplitPair, offsetSplitRoot, finiteFixedOffset, finiteFixedSpacing, nextN, nextJ, coeff_add, coeff_C_mul, coeff_X_mul, eval_add, eval_mul, eval_C, eval_X]
  have hp2 : p.coeff 2 = (12064 : ℝ) := by
    norm_num [p, arbitrarySplitPair, offsetSplitRoot, finiteFixedOffset, finiteFixedSpacing, nextN, nextJ, coeff_add, coeff_C_mul, coeff_X_mul, eval_add, eval_mul, eval_C, eval_X]
  have hp3 : p.coeff 3 = (512 : ℝ) := by
    norm_num [p, arbitrarySplitPair, offsetSplitRoot, finiteFixedOffset, finiteFixedSpacing, nextN, nextJ, coeff_add, coeff_C_mul, coeff_X_mul, eval_add, eval_mul, eval_C, eval_X]
  have hq0 : q.coeff 0 = (315 : ℝ) / 16 := by
    norm_num [q, arbitrarySplitPair, offsetSplitRoot, finiteFixedOffset, finiteFixedSpacing, nextN, nextJ, coeff_add, coeff_C_mul, coeff_X_mul, eval_add, eval_mul, eval_C, eval_X]
  have hq1 : q.coeff 1 = (12546 : ℝ) := by
    norm_num [q, arbitrarySplitPair, offsetSplitRoot, finiteFixedOffset, finiteFixedSpacing, nextN, nextJ, coeff_add, coeff_C_mul, coeff_X_mul, eval_add, eval_mul, eval_C, eval_X]
  have hq2 : q.coeff 2 = (24544 : ℝ) := by
    norm_num [q, arbitrarySplitPair, offsetSplitRoot, finiteFixedOffset, finiteFixedSpacing, nextN, nextJ, coeff_add, coeff_C_mul, coeff_X_mul, eval_add, eval_mul, eval_C, eval_X]
  have hq3 : q.coeff 3 = (5120 : ℝ) := by
    norm_num [q, arbitrarySplitPair, offsetSplitRoot, finiteFixedOffset, finiteFixedSpacing, nextN, nextJ, coeff_add, coeff_C_mul, coeff_X_mul, eval_add, eval_mul, eval_C, eval_X]
  have hpe : p.eval 4 = (5199603 : ℝ) / 16 := by
    norm_num [p, arbitrarySplitPair, offsetSplitRoot, finiteFixedOffset, finiteFixedSpacing, nextN, nextJ, coeff_add, coeff_C_mul, coeff_X_mul, eval_add, eval_mul, eval_C, eval_X]
  have hqe : q.eval 4 = (12329403 : ℝ) / 16 := by
    norm_num [q, arbitrarySplitPair, offsetSplitRoot, finiteFixedOffset, finiteFixedSpacing, nextN, nextJ, coeff_add, coeff_C_mul, coeff_X_mul, eval_add, eval_mul, eval_C, eval_X]
  have hd0 : D.coeff 0 = (1637874945 : ℝ) / 64 := by
    change (rawD p q 4).coeff 0 = _
    rw [finiteRawD_coeff_zero p q 4 (by norm_num), hpe, hq0]
    norm_num
  have hd1 : D.coeff 1 = (90589694571 : ℝ) / 8 := by
    change (rawD p q 4).coeff (0 + 1) = _
    rw [finiteRawD_coeff_succ p q 4 (by norm_num) 0,
      ← hD_eq, hpe, hq1, hd0, hqe, hp0]
    norm_num
  have hd2 : D.coeff 2 = (16876166424 : ℝ) := by
    change (rawD p q 4).coeff (1 + 1) = _
    rw [finiteRawD_coeff_succ p q 4 (by norm_num) 1,
      ← hD_eq, hpe, hq2, hd1, hqe, hp1]
    norm_num
  have hd3 : D.coeff 3 = (1578163584 : ℝ) := by
    change (rawD p q 4).coeff (2 + 1) = _
    rw [finiteRawD_coeff_succ p q 4 (by norm_num) 2,
      ← hD_eq, hpe, hq3, hd2, hqe, hp2]
    norm_num
  have hb0 : B.coeff 0 = (1521174206475 : ℝ) / 64 := by
    change (rawB p q 4).coeff 0 = _
    rw [finiteRawB_coeff p q 4 0, ← hD_eq, hd0, hpe, hqe, hp0, hq0]
    norm_num
  have hb1 : B.coeff 1 = (1771980942105 : ℝ) / 16 := by
    change (rawB p q 4).coeff 1 = _
    rw [finiteRawB_coeff p q 4 1, ← hD_eq, hd1, hpe, hqe, hp1, hq1]
    norm_num
  have hb2 : B.coeff 2 = (73813328160 : ℝ) := by
    change (rawB p q 4).coeff 2 = _
    rw [finiteRawB_coeff p q 4 2, ← hD_eq, hd2, hpe, hqe, hp2, hq2]
    norm_num
  have hb3 : B.coeff 3 = (294951360 : ℝ) := by
    change (rawB p q 4).coeff 3 = _
    rw [finiteRawB_coeff p q 4 3, ← hD_eq, hd3, hpe, hqe, hp3, hq3]
    norm_num
  refine ⟨?_, ?_, ?_⟩
  · intro i
    change D.coeff i = finiteFixedFourSite_DCoefficients i
    fin_cases i <;> norm_num [finiteFixedFourSite_DCoefficients, hd0, hd1, hd2, hd3]
  · intro i
    change B.coeff i = finiteFixedFourSite_BCoefficients i
    fin_cases i <;> norm_num [finiteFixedFourSite_BCoefficients, hb0, hb1, hb2, hb3]
  · apply finiteFixed_raw_dense_of_coeff_positive 3
    · intro j hj
      exact finiteFixed_root_gt_one_of_range 3 (by omega) (by omega) j
    · change ∀ i : Fin 4, 0 < D.coeff i
      intro i
      fin_cases i <;> norm_num [hd0, hd1, hd2, hd3]
    · change ∀ i : Fin 4, 0 < B.coeff i
      intro i
      fin_cases i <;> norm_num [hb0, hb1, hb2, hb3]

theorem finiteFixedFourSite_coefficients_positive :
    DensePositive (arbitrarySplitRawD 3 (finiteFixedOffset 3)
      (finiteFixedRadius 3) (finiteFixedSpacing 3)) 3 ∧
    DensePositive (arbitrarySplitRawB 3 (finiteFixedOffset 3)
      (finiteFixedRadius 3) (finiteFixedSpacing 3)) 3 :=
  finiteFixedFourSite_coefficients_exact.2.2

def finiteFixedFourSite_coalescedDCoefficients : Fin 4 → ℝ :=
  ![(87146496 : ℝ), (14377844736 : ℝ), (18388353024 : ℝ), (1652686848 : ℝ)]

theorem finiteFixedFourSite_coalesced_D_exact :
    (∀ i : Fin 4, (coalescedRawD 3 (finiteFixedRadius 3)).coeff i =
      finiteFixedFourSite_coalescedDCoefficients i) ∧
    (∀ i : Fin 4, 0 < (coalescedFiniteState 3 (finiteFixedRadius 3)).D i) := by
  let p := (coalescedPair 3).1
  let q := (coalescedPair 3).2
  let D := coalescedRawD 3 (finiteFixedRadius 3)
  have hD_eq : D = rawD p q 4 := rfl
  have hp0 : p.coeff 0 = (8128 : ℝ) := by
    norm_num [p, coalescedPair, nextN, nextJ, coeff_add, coeff_C_mul, coeff_X_mul, eval_add, eval_mul, eval_C, eval_X]
  have hp1 : p.coeff 1 = (25728 : ℝ) := by
    norm_num [p, coalescedPair, nextN, nextJ, coeff_add, coeff_C_mul, coeff_X_mul, eval_add, eval_mul, eval_C, eval_X]
  have hp2 : p.coeff 2 = (12288 : ℝ) := by
    norm_num [p, coalescedPair, nextN, nextJ, coeff_add, coeff_C_mul, coeff_X_mul, eval_add, eval_mul, eval_C, eval_X]
  have hq0 : q.coeff 0 = (64 : ℝ) := by
    norm_num [q, coalescedPair, nextN, nextJ, coeff_add, coeff_C_mul, coeff_X_mul, eval_add, eval_mul, eval_C, eval_X]
  have hq1 : q.coeff 1 = (15360 : ℝ) := by
    norm_num [q, coalescedPair, nextN, nextJ, coeff_add, coeff_C_mul, coeff_X_mul, eval_add, eval_mul, eval_C, eval_X]
  have hq2 : q.coeff 2 = (26112 : ℝ) := by
    norm_num [q, coalescedPair, nextN, nextJ, coeff_add, coeff_C_mul, coeff_X_mul, eval_add, eval_mul, eval_C, eval_X]
  have hq3 : q.coeff 3 = (5120 : ℝ) := by
    norm_num [q, coalescedPair, nextN, nextJ, coeff_add, coeff_C_mul, coeff_X_mul, eval_add, eval_mul, eval_C, eval_X]
  have hpe : p.eval 4 = (340416 : ℝ) := by
    norm_num [p, coalescedPair, nextN, nextJ, coeff_add, coeff_C_mul, coeff_X_mul, eval_add, eval_mul, eval_C, eval_X]
  have hqe : q.eval 4 = (806976 : ℝ) := by
    norm_num [q, coalescedPair, nextN, nextJ, coeff_add, coeff_C_mul, coeff_X_mul, eval_add, eval_mul, eval_C, eval_X]
  have hd0 : D.coeff 0 = (87146496 : ℝ) := by
    change (rawD p q 4).coeff 0 = _
    rw [finiteRawD_coeff_zero p q 4 (by norm_num), hpe, hq0]
    norm_num
  have hd1 : D.coeff 1 = (14377844736 : ℝ) := by
    change (rawD p q 4).coeff (0+1) = _
    rw [finiteRawD_coeff_succ p q 4 (by norm_num) 0, ← hD_eq, hpe, hq1, hd0, hqe, hp0]
    norm_num
  have hd2 : D.coeff 2 = (18388353024 : ℝ) := by
    change (rawD p q 4).coeff (1+1) = _
    rw [finiteRawD_coeff_succ p q 4 (by norm_num) 1, ← hD_eq, hpe, hq2, hd1, hqe, hp1]
    norm_num
  have hd3 : D.coeff 3 = (1652686848 : ℝ) := by
    change (rawD p q 4).coeff (2+1) = _
    rw [finiteRawD_coeff_succ p q 4 (by norm_num) 2, ← hD_eq, hpe, hq3, hd2, hqe, hp2]
    norm_num
  constructor
  · intro i
    change D.coeff i = finiteFixedFourSite_coalescedDCoefficients i
    fin_cases i <;> norm_num [finiteFixedFourSite_coalescedDCoefficients, hd0, hd1, hd2, hd3]
  · apply coalescedFiniteState_D_positive_of_coeff_positive 3 (finiteFixedRadius 3)
    change ∀ i : Fin 4, 0 < D.coeff i
    intro i
    fin_cases i <;> norm_num [hd0, hd1, hd2, hd3]

theorem finiteFixedFourSite_coalesced_D_positive :
    ∀ i : Fin 4, 0 < (coalescedFiniteState 3 (finiteFixedRadius 3)).D i :=
  finiteFixedFourSite_coalesced_D_exact.2

end
end PhosphorylationStableCapacity
