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

def finiteFixedFiveSite_DCoefficients : Fin 5 → ℝ :=
  ![(24210781654838625 : ℝ) / 262144, (3537232785215956575 : ℝ) / 32768, (340522789631824485 : ℝ) / 1024, (674469240343045 : ℝ) / 4, (8755960070480 : ℝ)]
def finiteFixedFiveSite_BCoefficients : Fin 5 → ℝ :=
  ![(115298027485775827875 : ℝ) / 262144, (192673109659169189925 : ℝ) / 65536, (1134171066406063455 : ℝ) / 256, (11444447720160105 : ℝ) / 8, (28630772010960 : ℝ)]

/-- Exact coefficient lookup and positivity for the printed n=5 family. -/
theorem finiteFixedFiveSite_coefficients_exact :
    (∀ i : Fin 5, (arbitrarySplitRawD 4 (finiteFixedOffset 4)
      (finiteFixedRadius 4) (finiteFixedSpacing 4)).coeff i = finiteFixedFiveSite_DCoefficients i) ∧
    (∀ i : Fin 5, (arbitrarySplitRawB 4 (finiteFixedOffset 4)
      (finiteFixedRadius 4) (finiteFixedSpacing 4)).coeff i = finiteFixedFiveSite_BCoefficients i) ∧
    DensePositive
      (arbitrarySplitRawD 4 (finiteFixedOffset 4)
        (finiteFixedRadius 4) (finiteFixedSpacing 4)) 4 ∧
    DensePositive
      (arbitrarySplitRawB 4 (finiteFixedOffset 4)
        (finiteFixedRadius 4) (finiteFixedSpacing 4)) 4 := by
  let p := (arbitrarySplitPair 4 (finiteFixedOffset 4)
    (finiteFixedSpacing 4)).1
  let q := (arbitrarySplitPair 4 (finiteFixedOffset 4)
    (finiteFixedSpacing 4)).2
  let D := arbitrarySplitRawD 4 (finiteFixedOffset 4)
    (finiteFixedRadius 4) (finiteFixedSpacing 4)
  let B := arbitrarySplitRawB 4 (finiteFixedOffset 4)
    (finiteFixedRadius 4) (finiteFixedSpacing 4)
  have hD_eq : D = rawD p q 8 := rfl
  have hp0 : p.coeff 0 = (118885725 : ℝ) / 1024 := by
    norm_num [p, arbitrarySplitPair, offsetSplitRoot, finiteFixedOffset, finiteFixedSpacing, nextN, nextJ, coeff_add, coeff_C_mul, coeff_X_mul, eval_add, eval_mul, eval_C, eval_X]
  have hp1 : p.coeff 1 = (78532515 : ℝ) / 128 := by
    norm_num [p, arbitrarySplitPair, offsetSplitRoot, finiteFixedOffset, finiteFixedSpacing, nextN, nextJ, coeff_add, coeff_C_mul, coeff_X_mul, eval_add, eval_mul, eval_C, eval_X]
  have hp2 : p.coeff 2 = (2771217 : ℝ) / 4 := by
    norm_num [p, arbitrarySplitPair, offsetSplitRoot, finiteFixedOffset, finiteFixedSpacing, nextN, nextJ, coeff_add, coeff_C_mul, coeff_X_mul, eval_add, eval_mul, eval_C, eval_X]
  have hp3 : p.coeff 3 = (166976 : ℝ) := by
    norm_num [p, arbitrarySplitPair, offsetSplitRoot, finiteFixedOffset, finiteFixedSpacing, nextN, nextJ, coeff_add, coeff_C_mul, coeff_X_mul, eval_add, eval_mul, eval_C, eval_X]
  have hp4 : p.coeff 4 = (4096 : ℝ) := by
    norm_num [p, arbitrarySplitPair, offsetSplitRoot, finiteFixedOffset, finiteFixedSpacing, nextN, nextJ, coeff_add, coeff_C_mul, coeff_X_mul, eval_add, eval_mul, eval_C, eval_X]
  have hq0 : q.coeff 0 = (155925 : ℝ) / 1024 := by
    norm_num [q, arbitrarySplitPair, offsetSplitRoot, finiteFixedOffset, finiteFixedSpacing, nextN, nextJ, coeff_add, coeff_C_mul, coeff_X_mul, eval_add, eval_mul, eval_C, eval_X]
  have hq1 : q.coeff 1 = (7331355 : ℝ) / 32 := by
    norm_num [q, arbitrarySplitPair, offsetSplitRoot, finiteFixedOffset, finiteFixedSpacing, nextN, nextJ, coeff_add, coeff_C_mul, coeff_X_mul, eval_add, eval_mul, eval_C, eval_X]
  have hq2 : q.coeff 2 = (3185271 : ℝ) / 4 := by
    norm_num [q, arbitrarySplitPair, offsetSplitRoot, finiteFixedOffset, finiteFixedSpacing, nextN, nextJ, coeff_add, coeff_C_mul, coeff_X_mul, eval_add, eval_mul, eval_C, eval_X]
  have hq3 : q.coeff 3 = (514688 : ℝ) := by
    norm_num [q, arbitrarySplitPair, offsetSplitRoot, finiteFixedOffset, finiteFixedSpacing, nextN, nextJ, coeff_add, coeff_C_mul, coeff_X_mul, eval_add, eval_mul, eval_C, eval_X]
  have hq4 : q.coeff 4 = (53248 : ℝ) := by
    norm_num [q, arbitrarySplitPair, offsetSplitRoot, finiteFixedOffset, finiteFixedSpacing, nextN, nextJ, coeff_add, coeff_C_mul, coeff_X_mul, eval_add, eval_mul, eval_C, eval_X]
  have hpe : p.eval 8 = (155271968285 : ℝ) / 1024 := by
    norm_num [p, arbitrarySplitPair, offsetSplitRoot, finiteFixedOffset, finiteFixedSpacing, nextN, nextJ, coeff_add, coeff_C_mul, coeff_X_mul, eval_add, eval_mul, eval_C, eval_X]
  have hqe : q.eval 8 = (547247504405 : ℝ) / 1024 := by
    norm_num [q, arbitrarySplitPair, offsetSplitRoot, finiteFixedOffset, finiteFixedSpacing, nextN, nextJ, coeff_add, coeff_C_mul, coeff_X_mul, eval_add, eval_mul, eval_C, eval_X]
  have hd0 : D.coeff 0 = (24210781654838625 : ℝ) / 262144 := by
    change (rawD p q 8).coeff 0 = _
    rw [finiteRawD_coeff_zero p q 8 (by norm_num), hpe, hq0]
    norm_num
  have hd1 : D.coeff 1 = (3537232785215956575 : ℝ) / 32768 := by
    change (rawD p q 8).coeff (0 + 1) = _
    rw [finiteRawD_coeff_succ p q 8 (by norm_num) 0,
      ← hD_eq, hpe, hq1, hd0, hqe, hp0]
    norm_num
  have hd2 : D.coeff 2 = (340522789631824485 : ℝ) / 1024 := by
    change (rawD p q 8).coeff (1 + 1) = _
    rw [finiteRawD_coeff_succ p q 8 (by norm_num) 1,
      ← hD_eq, hpe, hq2, hd1, hqe, hp1]
    norm_num
  have hd3 : D.coeff 3 = (674469240343045 : ℝ) / 4 := by
    change (rawD p q 8).coeff (2 + 1) = _
    rw [finiteRawD_coeff_succ p q 8 (by norm_num) 2,
      ← hD_eq, hpe, hq3, hd2, hqe, hp2]
    norm_num
  have hd4 : D.coeff 4 = (8755960070480 : ℝ) := by
    change (rawD p q 8).coeff (3 + 1) = _
    rw [finiteRawD_coeff_succ p q 8 (by norm_num) 3,
      ← hD_eq, hpe, hq4, hd3, hqe, hp3]
    norm_num
  have hb0 : B.coeff 0 = (115298027485775827875 : ℝ) / 262144 := by
    change (rawB p q 8).coeff 0 = _
    rw [finiteRawB_coeff p q 8 0, ← hD_eq, hd0, hpe, hqe, hp0, hq0]
    norm_num
  have hb1 : B.coeff 1 = (192673109659169189925 : ℝ) / 65536 := by
    change (rawB p q 8).coeff 1 = _
    rw [finiteRawB_coeff p q 8 1, ← hD_eq, hd1, hpe, hqe, hp1, hq1]
    norm_num
  have hb2 : B.coeff 2 = (1134171066406063455 : ℝ) / 256 := by
    change (rawB p q 8).coeff 2 = _
    rw [finiteRawB_coeff p q 8 2, ← hD_eq, hd2, hpe, hqe, hp2, hq2]
    norm_num
  have hb3 : B.coeff 3 = (11444447720160105 : ℝ) / 8 := by
    change (rawB p q 8).coeff 3 = _
    rw [finiteRawB_coeff p q 8 3, ← hD_eq, hd3, hpe, hqe, hp3, hq3]
    norm_num
  have hb4 : B.coeff 4 = (28630772010960 : ℝ) := by
    change (rawB p q 8).coeff 4 = _
    rw [finiteRawB_coeff p q 8 4, ← hD_eq, hd4, hpe, hqe, hp4, hq4]
    norm_num
  refine ⟨?_, ?_, ?_⟩
  · intro i
    change D.coeff i = finiteFixedFiveSite_DCoefficients i
    fin_cases i <;> norm_num [finiteFixedFiveSite_DCoefficients, hd0, hd1, hd2, hd3, hd4]
  · intro i
    change B.coeff i = finiteFixedFiveSite_BCoefficients i
    fin_cases i <;> norm_num [finiteFixedFiveSite_BCoefficients, hb0, hb1, hb2, hb3, hb4]
  · apply finiteFixed_raw_dense_of_coeff_positive 4
    · intro j hj
      exact finiteFixed_root_gt_one_of_range 4 (by omega) (by omega) j
    · change ∀ i : Fin 5, 0 < D.coeff i
      intro i
      fin_cases i <;> norm_num [hd0, hd1, hd2, hd3, hd4]
    · change ∀ i : Fin 5, 0 < B.coeff i
      intro i
      fin_cases i <;> norm_num [hb0, hb1, hb2, hb3, hb4]

theorem finiteFixedFiveSite_coefficients_positive :
    DensePositive (arbitrarySplitRawD 4 (finiteFixedOffset 4)
      (finiteFixedRadius 4) (finiteFixedSpacing 4)) 4 ∧
    DensePositive (arbitrarySplitRawB 4 (finiteFixedOffset 4)
      (finiteFixedRadius 4) (finiteFixedSpacing 4)) 4 :=
  finiteFixedFiveSite_coefficients_exact.2.2

def finiteFixedFiveSite_coalescedDCoefficients : Fin 5 → ℝ :=
  ![(157684596736 : ℝ), (122840549949440 : ℝ), (356366316208128 : ℝ), (173271299391488 : ℝ), (8890989150208 : ℝ)]

theorem finiteFixedFiveSite_coalesced_D_exact :
    (∀ i : Fin 5, (coalescedRawD 4 (finiteFixedRadius 4)).coeff i =
      finiteFixedFiveSite_coalescedDCoefficients i) ∧
    (∀ i : Fin 5, 0 < (coalescedFiniteState 4 (finiteFixedRadius 4)).D i) := by
  let p := (coalescedPair 4).1
  let q := (coalescedPair 4).2
  let D := coalescedRawD 4 (finiteFixedRadius 4)
  have hD_eq : D = rawD p q 8 := rfl
  have hp0 : p.coeff 0 = (130816 : ℝ) := by
    norm_num [p, coalescedPair, nextN, nextJ, coeff_add, coeff_C_mul, coeff_X_mul, eval_add, eval_mul, eval_C, eval_X]
  have hp1 : p.coeff 1 = (660992 : ℝ) := by
    norm_num [p, coalescedPair, nextN, nextJ, coeff_add, coeff_C_mul, coeff_X_mul, eval_add, eval_mul, eval_C, eval_X]
  have hp2 : p.coeff 2 = (715776 : ℝ) := by
    norm_num [p, coalescedPair, nextN, nextJ, coeff_add, coeff_C_mul, coeff_X_mul, eval_add, eval_mul, eval_C, eval_X]
  have hp3 : p.coeff 3 = (167936 : ℝ) := by
    norm_num [p, coalescedPair, nextN, nextJ, coeff_add, coeff_C_mul, coeff_X_mul, eval_add, eval_mul, eval_C, eval_X]
  have hq0 : q.coeff 0 = (256 : ℝ) := by
    norm_num [q, coalescedPair, nextN, nextJ, coeff_add, coeff_C_mul, coeff_X_mul, eval_add, eval_mul, eval_C, eval_X]
  have hq1 : q.coeff 1 = (257024 : ℝ) := by
    norm_num [q, coalescedPair, nextN, nextJ, coeff_add, coeff_C_mul, coeff_X_mul, eval_add, eval_mul, eval_C, eval_X]
  have hq2 : q.coeff 2 = (844800 : ℝ) := by
    norm_num [q, coalescedPair, nextN, nextJ, coeff_add, coeff_C_mul, coeff_X_mul, eval_add, eval_mul, eval_C, eval_X]
  have hq3 : q.coeff 3 = (524288 : ℝ) := by
    norm_num [q, coalescedPair, nextN, nextJ, coeff_add, coeff_C_mul, coeff_X_mul, eval_add, eval_mul, eval_C, eval_X]
  have hq4 : q.coeff 4 = (53248 : ℝ) := by
    norm_num [q, coalescedPair, nextN, nextJ, coeff_add, coeff_C_mul, coeff_X_mul, eval_add, eval_mul, eval_C, eval_X]
  have hpe : p.eval 8 = (153988864 : ℝ) := by
    norm_num [p, coalescedPair, nextN, nextJ, coeff_add, coeff_C_mul, coeff_X_mul, eval_add, eval_mul, eval_C, eval_X]
  have hqe : q.eval 8 = (542662912 : ℝ) := by
    norm_num [q, coalescedPair, nextN, nextJ, coeff_add, coeff_C_mul, coeff_X_mul, eval_add, eval_mul, eval_C, eval_X]
  have hd0 : D.coeff 0 = (157684596736 : ℝ) := by
    change (rawD p q 8).coeff 0 = _
    rw [finiteRawD_coeff_zero p q 8 (by norm_num), hpe, hq0]
    norm_num
  have hd1 : D.coeff 1 = (122840549949440 : ℝ) := by
    change (rawD p q 8).coeff (0+1) = _
    rw [finiteRawD_coeff_succ p q 8 (by norm_num) 0, ← hD_eq, hpe, hq1, hd0, hqe, hp0]
    norm_num
  have hd2 : D.coeff 2 = (356366316208128 : ℝ) := by
    change (rawD p q 8).coeff (1+1) = _
    rw [finiteRawD_coeff_succ p q 8 (by norm_num) 1, ← hD_eq, hpe, hq2, hd1, hqe, hp1]
    norm_num
  have hd3 : D.coeff 3 = (173271299391488 : ℝ) := by
    change (rawD p q 8).coeff (2+1) = _
    rw [finiteRawD_coeff_succ p q 8 (by norm_num) 2, ← hD_eq, hpe, hq3, hd2, hqe, hp2]
    norm_num
  have hd4 : D.coeff 4 = (8890989150208 : ℝ) := by
    change (rawD p q 8).coeff (3+1) = _
    rw [finiteRawD_coeff_succ p q 8 (by norm_num) 3, ← hD_eq, hpe, hq4, hd3, hqe, hp3]
    norm_num
  constructor
  · intro i
    change D.coeff i = finiteFixedFiveSite_coalescedDCoefficients i
    fin_cases i <;> norm_num [finiteFixedFiveSite_coalescedDCoefficients, hd0, hd1, hd2, hd3, hd4]
  · apply coalescedFiniteState_D_positive_of_coeff_positive 4 (finiteFixedRadius 4)
    change ∀ i : Fin 5, 0 < D.coeff i
    intro i
    fin_cases i <;> norm_num [hd0, hd1, hd2, hd3, hd4]

theorem finiteFixedFiveSite_coalesced_D_positive :
    ∀ i : Fin 5, 0 < (coalescedFiniteState 4 (finiteFixedRadius 4)).D i :=
  finiteFixedFiveSite_coalesced_D_exact.2

end
end PhosphorylationStableCapacity
