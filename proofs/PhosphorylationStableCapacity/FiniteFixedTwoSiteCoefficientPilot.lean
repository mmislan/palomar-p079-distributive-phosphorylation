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

def finiteFixedTwoSite_DCoefficients : Fin 2 → ℝ :=
  ![(2625 : ℝ) / 4, (2168 : ℝ)]
def finiteFixedTwoSite_BCoefficients : Fin 2 → ℝ :=
  ![(27027 : ℝ) / 4, (1716 : ℝ)]

/-- Exact coefficient lookup and positivity for the printed n=2 family. -/
theorem finiteFixedTwoSite_coefficients_exact :
    (∀ i : Fin 2, (arbitrarySplitRawD 1 (finiteFixedOffset 1)
      (finiteFixedRadius 1) (finiteFixedSpacing 1)).coeff i = finiteFixedTwoSite_DCoefficients i) ∧
    (∀ i : Fin 2, (arbitrarySplitRawB 1 (finiteFixedOffset 1)
      (finiteFixedRadius 1) (finiteFixedSpacing 1)).coeff i = finiteFixedTwoSite_BCoefficients i) ∧
    DensePositive
      (arbitrarySplitRawD 1 (finiteFixedOffset 1)
        (finiteFixedRadius 1) (finiteFixedSpacing 1)) 1 ∧
    DensePositive
      (arbitrarySplitRawB 1 (finiteFixedOffset 1)
        (finiteFixedRadius 1) (finiteFixedSpacing 1)) 1 := by
  let p := (arbitrarySplitPair 1 (finiteFixedOffset 1)
    (finiteFixedSpacing 1)).1
  let q := (arbitrarySplitPair 1 (finiteFixedOffset 1)
    (finiteFixedSpacing 1)).2
  let D := arbitrarySplitRawD 1 (finiteFixedOffset 1)
    (finiteFixedRadius 1) (finiteFixedSpacing 1)
  let B := arbitrarySplitRawB 1 (finiteFixedOffset 1)
    (finiteFixedRadius 1) (finiteFixedSpacing 1)
  have hD_eq : D = rawD p q 2 := rfl
  have hp0 : p.coeff 0 = (111 : ℝ) / 4 := by
    norm_num [p, arbitrarySplitPair, offsetSplitRoot, finiteFixedOffset, finiteFixedSpacing, nextN, nextJ, coeff_add, coeff_C_mul, coeff_X_mul, eval_add, eval_mul, eval_C, eval_X]
  have hp1 : p.coeff 1 = (8 : ℝ) := by
    norm_num [p, arbitrarySplitPair, offsetSplitRoot, finiteFixedOffset, finiteFixedSpacing, nextN, nextJ, coeff_add, coeff_C_mul, coeff_X_mul, eval_add, eval_mul, eval_C, eval_X]
  have hq0 : q.coeff 0 = (15 : ℝ) / 4 := by
    norm_num [q, arbitrarySplitPair, offsetSplitRoot, finiteFixedOffset, finiteFixedSpacing, nextN, nextJ, coeff_add, coeff_C_mul, coeff_X_mul, eval_add, eval_mul, eval_C, eval_X]
  have hq1 : q.coeff 1 = (32 : ℝ) := by
    norm_num [q, arbitrarySplitPair, offsetSplitRoot, finiteFixedOffset, finiteFixedSpacing, nextN, nextJ, coeff_add, coeff_C_mul, coeff_X_mul, eval_add, eval_mul, eval_C, eval_X]
  have hpe : p.eval 2 = (175 : ℝ) / 4 := by
    norm_num [p, arbitrarySplitPair, offsetSplitRoot, finiteFixedOffset, finiteFixedSpacing, nextN, nextJ, coeff_add, coeff_C_mul, coeff_X_mul, eval_add, eval_mul, eval_C, eval_X]
  have hqe : q.eval 2 = (271 : ℝ) / 4 := by
    norm_num [q, arbitrarySplitPair, offsetSplitRoot, finiteFixedOffset, finiteFixedSpacing, nextN, nextJ, coeff_add, coeff_C_mul, coeff_X_mul, eval_add, eval_mul, eval_C, eval_X]
  have hd0 : D.coeff 0 = (2625 : ℝ) / 4 := by
    change (rawD p q 2).coeff 0 = _
    rw [finiteRawD_coeff_zero p q 2 (by norm_num), hpe, hq0]
    norm_num
  have hd1 : D.coeff 1 = (2168 : ℝ) := by
    change (rawD p q 2).coeff (0 + 1) = _
    rw [finiteRawD_coeff_succ p q 2 (by norm_num) 0,
      ← hD_eq, hpe, hq1, hd0, hqe, hp0]
    norm_num
  have hb0 : B.coeff 0 = (27027 : ℝ) / 4 := by
    change (rawB p q 2).coeff 0 = _
    rw [finiteRawB_coeff p q 2 0, ← hD_eq, hd0, hpe, hqe, hp0, hq0]
    norm_num
  have hb1 : B.coeff 1 = (1716 : ℝ) := by
    change (rawB p q 2).coeff 1 = _
    rw [finiteRawB_coeff p q 2 1, ← hD_eq, hd1, hpe, hqe, hp1, hq1]
    norm_num
  refine ⟨?_, ?_, ?_⟩
  · intro i
    change D.coeff i = finiteFixedTwoSite_DCoefficients i
    fin_cases i <;> norm_num [finiteFixedTwoSite_DCoefficients, hd0, hd1]
  · intro i
    change B.coeff i = finiteFixedTwoSite_BCoefficients i
    fin_cases i <;> norm_num [finiteFixedTwoSite_BCoefficients, hb0, hb1]
  · apply finiteFixed_raw_dense_of_coeff_positive 1
    · intro j hj
      exact finiteFixed_root_gt_one_of_range 1 (by omega) (by omega) j
    · change ∀ i : Fin 2, 0 < D.coeff i
      intro i
      fin_cases i <;> norm_num [hd0, hd1]
    · change ∀ i : Fin 2, 0 < B.coeff i
      intro i
      fin_cases i <;> norm_num [hb0, hb1]

theorem finiteFixedTwoSite_coefficients_positive :
    DensePositive (arbitrarySplitRawD 1 (finiteFixedOffset 1)
      (finiteFixedRadius 1) (finiteFixedSpacing 1)) 1 ∧
    DensePositive (arbitrarySplitRawB 1 (finiteFixedOffset 1)
      (finiteFixedRadius 1) (finiteFixedSpacing 1)) 1 :=
  finiteFixedTwoSite_coefficients_exact.2.2

def finiteFixedTwoSite_coalescedDCoefficients : Fin 2 → ℝ :=
  ![(704 : ℝ), (2176 : ℝ)]

theorem finiteFixedTwoSite_coalesced_D_exact :
    (∀ i : Fin 2, (coalescedRawD 1 (finiteFixedRadius 1)).coeff i =
      finiteFixedTwoSite_coalescedDCoefficients i) ∧
    (∀ i : Fin 2, 0 < (coalescedFiniteState 1 (finiteFixedRadius 1)).D i) := by
  let p := (coalescedPair 1).1
  let q := (coalescedPair 1).2
  let D := coalescedRawD 1 (finiteFixedRadius 1)
  have hD_eq : D = rawD p q 2 := rfl
  have hp0 : p.coeff 0 = (28 : ℝ) := by
    norm_num [p, coalescedPair, nextN, nextJ, coeff_add, coeff_C_mul, coeff_X_mul, eval_add, eval_mul, eval_C, eval_X]
  have hq0 : q.coeff 0 = (4 : ℝ) := by
    norm_num [q, coalescedPair, nextN, nextJ, coeff_add, coeff_C_mul, coeff_X_mul, eval_add, eval_mul, eval_C, eval_X]
  have hq1 : q.coeff 1 = (32 : ℝ) := by
    norm_num [q, coalescedPair, nextN, nextJ, coeff_add, coeff_C_mul, coeff_X_mul, eval_add, eval_mul, eval_C, eval_X]
  have hpe : p.eval 2 = (44 : ℝ) := by
    norm_num [p, coalescedPair, nextN, nextJ, coeff_add, coeff_C_mul, coeff_X_mul, eval_add, eval_mul, eval_C, eval_X]
  have hqe : q.eval 2 = (68 : ℝ) := by
    norm_num [q, coalescedPair, nextN, nextJ, coeff_add, coeff_C_mul, coeff_X_mul, eval_add, eval_mul, eval_C, eval_X]
  have hd0 : D.coeff 0 = (704 : ℝ) := by
    change (rawD p q 2).coeff 0 = _
    rw [finiteRawD_coeff_zero p q 2 (by norm_num), hpe, hq0]
    norm_num
  have hd1 : D.coeff 1 = (2176 : ℝ) := by
    change (rawD p q 2).coeff (0+1) = _
    rw [finiteRawD_coeff_succ p q 2 (by norm_num) 0, ← hD_eq, hpe, hq1, hd0, hqe, hp0]
    norm_num
  constructor
  · intro i
    change D.coeff i = finiteFixedTwoSite_coalescedDCoefficients i
    fin_cases i <;> norm_num [finiteFixedTwoSite_coalescedDCoefficients, hd0, hd1]
  · apply coalescedFiniteState_D_positive_of_coeff_positive 1 (finiteFixedRadius 1)
    change ∀ i : Fin 2, 0 < D.coeff i
    intro i
    fin_cases i <;> norm_num [hd0, hd1]

theorem finiteFixedTwoSite_coalesced_D_positive :
    ∀ i : Fin 2, 0 < (coalescedFiniteState 1 (finiteFixedRadius 1)).D i :=
  finiteFixedTwoSite_coalesced_D_exact.2

end
end PhosphorylationStableCapacity
