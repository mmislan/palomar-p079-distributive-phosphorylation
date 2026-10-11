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

def finiteFixedThreeSite_DCoefficients : Fin 3 → ℝ :=
  ![(790065 : ℝ) / 4, (9181854 : ℝ), (2648896 : ℝ)]
def finiteFixedThreeSite_BCoefficients : Fin 3 → ℝ :=
  ![(93618315 : ℝ) / 4, (56298693 : ℝ), (4494592 : ℝ)]

/-- Exact coefficient lookup and positivity for the printed n=3 family. -/
theorem finiteFixedThreeSite_coefficients_exact :
    (∀ i : Fin 3, (arbitrarySplitRawD 2 (finiteFixedOffset 2)
      (finiteFixedRadius 2) (finiteFixedSpacing 2)).coeff i = finiteFixedThreeSite_DCoefficients i) ∧
    (∀ i : Fin 3, (arbitrarySplitRawB 2 (finiteFixedOffset 2)
      (finiteFixedRadius 2) (finiteFixedSpacing 2)).coeff i = finiteFixedThreeSite_BCoefficients i) ∧
    DensePositive
      (arbitrarySplitRawD 2 (finiteFixedOffset 2)
        (finiteFixedRadius 2) (finiteFixedSpacing 2)) 2 ∧
    DensePositive
      (arbitrarySplitRawB 2 (finiteFixedOffset 2)
        (finiteFixedRadius 2) (finiteFixedSpacing 2)) 2 := by
  let p := (arbitrarySplitPair 2 (finiteFixedOffset 2)
    (finiteFixedSpacing 2)).1
  let q := (arbitrarySplitPair 2 (finiteFixedOffset 2)
    (finiteFixedSpacing 2)).2
  let D := arbitrarySplitRawD 2 (finiteFixedOffset 2)
    (finiteFixedRadius 2) (finiteFixedSpacing 2)
  let B := arbitrarySplitRawB 2 (finiteFixedOffset 2)
    (finiteFixedRadius 2) (finiteFixedSpacing 2)
  have hD_eq : D = rawD p q 4 := rfl
  have hp0 : p.coeff 0 = (1845 : ℝ) / 4 := by
    norm_num [p, arbitrarySplitPair, offsetSplitRoot, finiteFixedOffset, finiteFixedSpacing, nextN, nextJ, coeff_add, coeff_C_mul, coeff_X_mul, eval_add, eval_mul, eval_C, eval_X]
  have hp1 : p.coeff 1 = (726 : ℝ) := by
    norm_num [p, arbitrarySplitPair, offsetSplitRoot, finiteFixedOffset, finiteFixedSpacing, nextN, nextJ, coeff_add, coeff_C_mul, coeff_X_mul, eval_add, eval_mul, eval_C, eval_X]
  have hp2 : p.coeff 2 = (64 : ℝ) := by
    norm_num [p, arbitrarySplitPair, offsetSplitRoot, finiteFixedOffset, finiteFixedSpacing, nextN, nextJ, coeff_add, coeff_C_mul, coeff_X_mul, eval_add, eval_mul, eval_C, eval_X]
  have hq0 : q.coeff 0 = (45 : ℝ) / 4 := by
    norm_num [q, arbitrarySplitPair, offsetSplitRoot, finiteFixedOffset, finiteFixedSpacing, nextN, nextJ, coeff_add, coeff_C_mul, coeff_X_mul, eval_add, eval_mul, eval_C, eval_X]
  have hq1 : q.coeff 1 = (792 : ℝ) := by
    norm_num [q, arbitrarySplitPair, offsetSplitRoot, finiteFixedOffset, finiteFixedSpacing, nextN, nextJ, coeff_add, coeff_C_mul, coeff_X_mul, eval_add, eval_mul, eval_C, eval_X]
  have hq2 : q.coeff 2 = (448 : ℝ) := by
    norm_num [q, arbitrarySplitPair, offsetSplitRoot, finiteFixedOffset, finiteFixedSpacing, nextN, nextJ, coeff_add, coeff_C_mul, coeff_X_mul, eval_add, eval_mul, eval_C, eval_X]
  have hpe : p.eval 4 = (17557 : ℝ) / 4 := by
    norm_num [p, arbitrarySplitPair, offsetSplitRoot, finiteFixedOffset, finiteFixedSpacing, nextN, nextJ, coeff_add, coeff_C_mul, coeff_X_mul, eval_add, eval_mul, eval_C, eval_X]
  have hqe : q.eval 4 = (41389 : ℝ) / 4 := by
    norm_num [q, arbitrarySplitPair, offsetSplitRoot, finiteFixedOffset, finiteFixedSpacing, nextN, nextJ, coeff_add, coeff_C_mul, coeff_X_mul, eval_add, eval_mul, eval_C, eval_X]
  have hd0 : D.coeff 0 = (790065 : ℝ) / 4 := by
    change (rawD p q 4).coeff 0 = _
    rw [finiteRawD_coeff_zero p q 4 (by norm_num), hpe, hq0]
    norm_num
  have hd1 : D.coeff 1 = (9181854 : ℝ) := by
    change (rawD p q 4).coeff (0 + 1) = _
    rw [finiteRawD_coeff_succ p q 4 (by norm_num) 0,
      ← hD_eq, hpe, hq1, hd0, hqe, hp0]
    norm_num
  have hd2 : D.coeff 2 = (2648896 : ℝ) := by
    change (rawD p q 4).coeff (1 + 1) = _
    rw [finiteRawD_coeff_succ p q 4 (by norm_num) 1,
      ← hD_eq, hpe, hq2, hd1, hqe, hp1]
    norm_num
  have hb0 : B.coeff 0 = (93618315 : ℝ) / 4 := by
    change (rawB p q 4).coeff 0 = _
    rw [finiteRawB_coeff p q 4 0, ← hD_eq, hd0, hpe, hqe, hp0, hq0]
    norm_num
  have hb1 : B.coeff 1 = (56298693 : ℝ) := by
    change (rawB p q 4).coeff 1 = _
    rw [finiteRawB_coeff p q 4 1, ← hD_eq, hd1, hpe, hqe, hp1, hq1]
    norm_num
  have hb2 : B.coeff 2 = (4494592 : ℝ) := by
    change (rawB p q 4).coeff 2 = _
    rw [finiteRawB_coeff p q 4 2, ← hD_eq, hd2, hpe, hqe, hp2, hq2]
    norm_num
  refine ⟨?_, ?_, ?_⟩
  · intro i
    change D.coeff i = finiteFixedThreeSite_DCoefficients i
    fin_cases i <;> norm_num [finiteFixedThreeSite_DCoefficients, hd0, hd1, hd2]
  · intro i
    change B.coeff i = finiteFixedThreeSite_BCoefficients i
    fin_cases i <;> norm_num [finiteFixedThreeSite_BCoefficients, hb0, hb1, hb2]
  · apply finiteFixed_raw_dense_of_coeff_positive 2
    · intro j hj
      exact finiteFixed_root_gt_one_of_range 2 (by omega) (by omega) j
    · change ∀ i : Fin 3, 0 < D.coeff i
      intro i
      fin_cases i <;> norm_num [hd0, hd1, hd2]
    · change ∀ i : Fin 3, 0 < B.coeff i
      intro i
      fin_cases i <;> norm_num [hb0, hb1, hb2]

theorem finiteFixedThreeSite_coefficients_positive :
    DensePositive (arbitrarySplitRawD 2 (finiteFixedOffset 2)
      (finiteFixedRadius 2) (finiteFixedSpacing 2)) 2 ∧
    DensePositive (arbitrarySplitRawB 2 (finiteFixedOffset 2)
      (finiteFixedRadius 2) (finiteFixedSpacing 2)) 2 :=
  finiteFixedThreeSite_coefficients_exact.2.2

def finiteFixedThreeSite_coalescedDCoefficients : Fin 3 → ℝ :=
  ![(285696 : ℝ), (9713664 : ℝ), (2691072 : ℝ)]

theorem finiteFixedThreeSite_coalesced_D_exact :
    (∀ i : Fin 3, (coalescedRawD 2 (finiteFixedRadius 2)).coeff i =
      finiteFixedThreeSite_coalescedDCoefficients i) ∧
    (∀ i : Fin 3, 0 < (coalescedFiniteState 2 (finiteFixedRadius 2)).D i) := by
  let p := (coalescedPair 2).1
  let q := (coalescedPair 2).2
  let D := coalescedRawD 2 (finiteFixedRadius 2)
  have hD_eq : D = rawD p q 4 := rfl
  have hp0 : p.coeff 0 = (496 : ℝ) := by
    norm_num [p, coalescedPair, nextN, nextJ, coeff_add, coeff_C_mul, coeff_X_mul, eval_add, eval_mul, eval_C, eval_X]
  have hp1 : p.coeff 1 = (736 : ℝ) := by
    norm_num [p, coalescedPair, nextN, nextJ, coeff_add, coeff_C_mul, coeff_X_mul, eval_add, eval_mul, eval_C, eval_X]
  have hq0 : q.coeff 0 = (16 : ℝ) := by
    norm_num [q, coalescedPair, nextN, nextJ, coeff_add, coeff_C_mul, coeff_X_mul, eval_add, eval_mul, eval_C, eval_X]
  have hq1 : q.coeff 1 = (832 : ℝ) := by
    norm_num [q, coalescedPair, nextN, nextJ, coeff_add, coeff_C_mul, coeff_X_mul, eval_add, eval_mul, eval_C, eval_X]
  have hq2 : q.coeff 2 = (448 : ℝ) := by
    norm_num [q, coalescedPair, nextN, nextJ, coeff_add, coeff_C_mul, coeff_X_mul, eval_add, eval_mul, eval_C, eval_X]
  have hpe : p.eval 4 = (4464 : ℝ) := by
    norm_num [p, coalescedPair, nextN, nextJ, coeff_add, coeff_C_mul, coeff_X_mul, eval_add, eval_mul, eval_C, eval_X]
  have hqe : q.eval 4 = (10512 : ℝ) := by
    norm_num [q, coalescedPair, nextN, nextJ, coeff_add, coeff_C_mul, coeff_X_mul, eval_add, eval_mul, eval_C, eval_X]
  have hd0 : D.coeff 0 = (285696 : ℝ) := by
    change (rawD p q 4).coeff 0 = _
    rw [finiteRawD_coeff_zero p q 4 (by norm_num), hpe, hq0]
    norm_num
  have hd1 : D.coeff 1 = (9713664 : ℝ) := by
    change (rawD p q 4).coeff (0+1) = _
    rw [finiteRawD_coeff_succ p q 4 (by norm_num) 0, ← hD_eq, hpe, hq1, hd0, hqe, hp0]
    norm_num
  have hd2 : D.coeff 2 = (2691072 : ℝ) := by
    change (rawD p q 4).coeff (1+1) = _
    rw [finiteRawD_coeff_succ p q 4 (by norm_num) 1, ← hD_eq, hpe, hq2, hd1, hqe, hp1]
    norm_num
  constructor
  · intro i
    change D.coeff i = finiteFixedThreeSite_coalescedDCoefficients i
    fin_cases i <;> norm_num [finiteFixedThreeSite_coalescedDCoefficients, hd0, hd1, hd2]
  · apply coalescedFiniteState_D_positive_of_coeff_positive 2 (finiteFixedRadius 2)
    change ∀ i : Fin 3, 0 < D.coeff i
    intro i
    fin_cases i <;> norm_num [hd0, hd1, hd2]

theorem finiteFixedThreeSite_coalesced_D_positive :
    ∀ i : Fin 3, 0 < (coalescedFiniteState 2 (finiteFixedRadius 2)).D i :=
  finiteFixedThreeSite_coalesced_D_exact.2

end
end PhosphorylationStableCapacity
