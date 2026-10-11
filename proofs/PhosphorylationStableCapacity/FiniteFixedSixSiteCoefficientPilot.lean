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

def finiteFixedSixSite_DCoefficients : Fin 6 → ℝ :=
  ![(1823944506723206492625 : ℝ) / 67108864, (1600617671006831200598175 : ℝ) / 8388608, (255177448757516535695865 : ℝ) / 262144, (2267357582284751369805 : ℝ) / 2048, (4581474359034300875 : ℝ) / 16, (8469756670032280 : ℝ)]
def finiteFixedSixSite_BCoefficients : Fin 6 → ℝ :=
  ![(51426352106349766452781875 : ℝ) / 67108864, (114381633799277562797281125 : ℝ) / 16777216, (1085767660826876211705675 : ℝ) / 65536, (49863486844900381878225 : ℝ) / 4096, (34440874013457802275 : ℝ) / 16, (14961143491763700 : ℝ)]

/-- Exact coefficient lookup and positivity for the printed n=6 family. -/
theorem finiteFixedSixSite_coefficients_exact :
    (∀ i : Fin 6, (arbitrarySplitRawD 5 (finiteFixedOffset 5)
      (finiteFixedRadius 5) (finiteFixedSpacing 5)).coeff i = finiteFixedSixSite_DCoefficients i) ∧
    (∀ i : Fin 6, (arbitrarySplitRawB 5 (finiteFixedOffset 5)
      (finiteFixedRadius 5) (finiteFixedSpacing 5)).coeff i = finiteFixedSixSite_BCoefficients i) ∧
    DensePositive
      (arbitrarySplitRawD 5 (finiteFixedOffset 5)
        (finiteFixedRadius 5) (finiteFixedSpacing 5)) 5 ∧
    DensePositive
      (arbitrarySplitRawB 5 (finiteFixedOffset 5)
        (finiteFixedRadius 5) (finiteFixedSpacing 5)) 5 := by
  let p := (arbitrarySplitPair 5 (finiteFixedOffset 5)
    (finiteFixedSpacing 5)).1
  let q := (arbitrarySplitPair 5 (finiteFixedOffset 5)
    (finiteFixedSpacing 5)).2
  let D := arbitrarySplitRawD 5 (finiteFixedOffset 5)
    (finiteFixedRadius 5) (finiteFixedSpacing 5)
  let B := arbitrarySplitRawB 5 (finiteFixedOffset 5)
    (finiteFixedRadius 5) (finiteFixedSpacing 5)
  have hD_eq : D = rawD p q 8 := rfl
  have hp0 : p.coeff 0 = (27492540075 : ℝ) / 16384 := by
    norm_num [p, arbitrarySplitPair, offsetSplitRoot, finiteFixedOffset, finiteFixedSpacing, nextN, nextJ, coeff_add, coeff_C_mul, coeff_X_mul, eval_add, eval_mul, eval_C, eval_X]
  have hp1 : p.coeff 1 = (25673663205 : ℝ) / 2048 := by
    norm_num [p, arbitrarySplitPair, offsetSplitRoot, finiteFixedOffset, finiteFixedSpacing, nextN, nextJ, coeff_add, coeff_C_mul, coeff_X_mul, eval_add, eval_mul, eval_C, eval_X]
  have hp2 : p.coeff 2 = (1565853219 : ℝ) / 64 := by
    norm_num [p, arbitrarySplitPair, offsetSplitRoot, finiteFixedOffset, finiteFixedSpacing, nextN, nextJ, coeff_add, coeff_C_mul, coeff_X_mul, eval_add, eval_mul, eval_C, eval_X]
  have hp3 : p.coeff 3 = (14129406 : ℝ) := by
    norm_num [p, arbitrarySplitPair, offsetSplitRoot, finiteFixedOffset, finiteFixedSpacing, nextN, nextJ, coeff_add, coeff_C_mul, coeff_X_mul, eval_add, eval_mul, eval_C, eval_X]
  have hp4 : p.coeff 4 = (2033920 : ℝ) := by
    norm_num [p, arbitrarySplitPair, offsetSplitRoot, finiteFixedOffset, finiteFixedSpacing, nextN, nextJ, coeff_add, coeff_C_mul, coeff_X_mul, eval_add, eval_mul, eval_C, eval_X]
  have hp5 : p.coeff 5 = (32768 : ℝ) := by
    norm_num [p, arbitrarySplitPair, offsetSplitRoot, finiteFixedOffset, finiteFixedSpacing, nextN, nextJ, coeff_add, coeff_C_mul, coeff_X_mul, eval_add, eval_mul, eval_C, eval_X]
  have hq0 : q.coeff 0 = (6081075 : ℝ) / 16384 := by
    norm_num [q, arbitrarySplitPair, offsetSplitRoot, finiteFixedOffset, finiteFixedSpacing, nextN, nextJ, coeff_add, coeff_C_mul, coeff_X_mul, eval_add, eval_mul, eval_C, eval_X]
  have hq1 : q.coeff 1 = (1713175245 : ℝ) / 512 := by
    norm_num [q, arbitrarySplitPair, offsetSplitRoot, finiteFixedOffset, finiteFixedSpacing, nextN, nextJ, coeff_add, coeff_C_mul, coeff_X_mul, eval_add, eval_mul, eval_C, eval_X]
  have hq2 : q.coeff 2 = (1183917429 : ℝ) / 64 := by
    norm_num [q, arbitrarySplitPair, offsetSplitRoot, finiteFixedOffset, finiteFixedSpacing, nextN, nextJ, coeff_add, coeff_C_mul, coeff_X_mul, eval_add, eval_mul, eval_C, eval_X]
  have hq3 : q.coeff 3 = (24252396 : ℝ) := by
    norm_num [q, arbitrarySplitPair, offsetSplitRoot, finiteFixedOffset, finiteFixedSpacing, nextN, nextJ, coeff_add, coeff_C_mul, coeff_X_mul, eval_add, eval_mul, eval_C, eval_X]
  have hq4 : q.coeff 4 = (8254720 : ℝ) := by
    norm_num [q, arbitrarySplitPair, offsetSplitRoot, finiteFixedOffset, finiteFixedSpacing, nextN, nextJ, coeff_add, coeff_C_mul, coeff_X_mul, eval_add, eval_mul, eval_C, eval_X]
  have hq5 : q.coeff 5 = (524288 : ℝ) := by
    norm_num [q, arbitrarySplitPair, offsetSplitRoot, finiteFixedOffset, finiteFixedSpacing, nextN, nextJ, coeff_add, coeff_C_mul, coeff_X_mul, eval_add, eval_mul, eval_C, eval_X]
  have hpe : p.eval 8 = (299937841043435 : ℝ) / 16384 := by
    norm_num [p, arbitrarySplitPair, offsetSplitRoot, finiteFixedOffset, finiteFixedSpacing, nextN, nextJ, coeff_add, coeff_C_mul, coeff_X_mul, eval_add, eval_mul, eval_C, eval_X]
  have hqe : q.eval 8 = (1058719583754035 : ℝ) / 16384 := by
    norm_num [q, arbitrarySplitPair, offsetSplitRoot, finiteFixedOffset, finiteFixedSpacing, nextN, nextJ, coeff_add, coeff_C_mul, coeff_X_mul, eval_add, eval_mul, eval_C, eval_X]
  have hd0 : D.coeff 0 = (1823944506723206492625 : ℝ) / 67108864 := by
    change (rawD p q 8).coeff 0 = _
    rw [finiteRawD_coeff_zero p q 8 (by norm_num), hpe, hq0]
    norm_num
  have hd1 : D.coeff 1 = (1600617671006831200598175 : ℝ) / 8388608 := by
    change (rawD p q 8).coeff (0 + 1) = _
    rw [finiteRawD_coeff_succ p q 8 (by norm_num) 0,
      ← hD_eq, hpe, hq1, hd0, hqe, hp0]
    norm_num
  have hd2 : D.coeff 2 = (255177448757516535695865 : ℝ) / 262144 := by
    change (rawD p q 8).coeff (1 + 1) = _
    rw [finiteRawD_coeff_succ p q 8 (by norm_num) 1,
      ← hD_eq, hpe, hq2, hd1, hqe, hp1]
    norm_num
  have hd3 : D.coeff 3 = (2267357582284751369805 : ℝ) / 2048 := by
    change (rawD p q 8).coeff (2 + 1) = _
    rw [finiteRawD_coeff_succ p q 8 (by norm_num) 2,
      ← hD_eq, hpe, hq3, hd2, hqe, hp2]
    norm_num
  have hd4 : D.coeff 4 = (4581474359034300875 : ℝ) / 16 := by
    change (rawD p q 8).coeff (3 + 1) = _
    rw [finiteRawD_coeff_succ p q 8 (by norm_num) 3,
      ← hD_eq, hpe, hq4, hd3, hqe, hp3]
    norm_num
  have hd5 : D.coeff 5 = (8469756670032280 : ℝ) := by
    change (rawD p q 8).coeff (4 + 1) = _
    rw [finiteRawD_coeff_succ p q 8 (by norm_num) 4,
      ← hD_eq, hpe, hq5, hd4, hqe, hp4]
    norm_num
  have hb0 : B.coeff 0 = (51426352106349766452781875 : ℝ) / 67108864 := by
    change (rawB p q 8).coeff 0 = _
    rw [finiteRawB_coeff p q 8 0, ← hD_eq, hd0, hpe, hqe, hp0, hq0]
    norm_num
  have hb1 : B.coeff 1 = (114381633799277562797281125 : ℝ) / 16777216 := by
    change (rawB p q 8).coeff 1 = _
    rw [finiteRawB_coeff p q 8 1, ← hD_eq, hd1, hpe, hqe, hp1, hq1]
    norm_num
  have hb2 : B.coeff 2 = (1085767660826876211705675 : ℝ) / 65536 := by
    change (rawB p q 8).coeff 2 = _
    rw [finiteRawB_coeff p q 8 2, ← hD_eq, hd2, hpe, hqe, hp2, hq2]
    norm_num
  have hb3 : B.coeff 3 = (49863486844900381878225 : ℝ) / 4096 := by
    change (rawB p q 8).coeff 3 = _
    rw [finiteRawB_coeff p q 8 3, ← hD_eq, hd3, hpe, hqe, hp3, hq3]
    norm_num
  have hb4 : B.coeff 4 = (34440874013457802275 : ℝ) / 16 := by
    change (rawB p q 8).coeff 4 = _
    rw [finiteRawB_coeff p q 8 4, ← hD_eq, hd4, hpe, hqe, hp4, hq4]
    norm_num
  have hb5 : B.coeff 5 = (14961143491763700 : ℝ) := by
    change (rawB p q 8).coeff 5 = _
    rw [finiteRawB_coeff p q 8 5, ← hD_eq, hd5, hpe, hqe, hp5, hq5]
    norm_num
  refine ⟨?_, ?_, ?_⟩
  · intro i
    change D.coeff i = finiteFixedSixSite_DCoefficients i
    fin_cases i <;> norm_num [finiteFixedSixSite_DCoefficients, hd0, hd1, hd2, hd3, hd4, hd5]
  · intro i
    change B.coeff i = finiteFixedSixSite_BCoefficients i
    fin_cases i <;> norm_num [finiteFixedSixSite_BCoefficients, hb0, hb1, hb2, hb3, hb4, hb5]
  · apply finiteFixed_raw_dense_of_coeff_positive 5
    · intro j hj
      exact finiteFixed_root_gt_one_of_range 5 (by omega) (by omega) j
    · change ∀ i : Fin 6, 0 < D.coeff i
      intro i
      fin_cases i <;> norm_num [hd0, hd1, hd2, hd3, hd4, hd5]
    · change ∀ i : Fin 6, 0 < B.coeff i
      intro i
      fin_cases i <;> norm_num [hb0, hb1, hb2, hb3, hb4, hb5]

theorem finiteFixedSixSite_coefficients_positive :
    DensePositive (arbitrarySplitRawD 5 (finiteFixedOffset 5)
      (finiteFixedRadius 5) (finiteFixedSpacing 5)) 5 ∧
    DensePositive (arbitrarySplitRawB 5 (finiteFixedOffset 5)
      (finiteFixedRadius 5) (finiteFixedSpacing 5)) 5 :=
  finiteFixedSixSite_coefficients_exact.2.2

def finiteFixedSixSite_coalescedDCoefficients : Fin 6 → ℝ :=
  ![(77132038406144 : ℝ), (244429694991073280 : ℝ), (1146145836980240384 : ℝ), (1211025563897036800 : ℝ), (298259980358778880 : ℝ), (8711954747097088 : ℝ)]

theorem finiteFixedSixSite_coalesced_D_exact :
    (∀ i : Fin 6, (coalescedRawD 5 (finiteFixedRadius 5)).coeff i =
      finiteFixedSixSite_coalescedDCoefficients i) ∧
    (∀ i : Fin 6, 0 < (coalescedFiniteState 5 (finiteFixedRadius 5)).D i) := by
  let p := (coalescedPair 5).1
  let q := (coalescedPair 5).2
  let D := coalescedRawD 5 (finiteFixedRadius 5)
  have hD_eq : D = rawD p q 8 := rfl
  have hp0 : p.coeff 0 = (2096128 : ℝ) := by
    norm_num [p, coalescedPair, nextN, nextJ, coeff_add, coeff_C_mul, coeff_X_mul, eval_add, eval_mul, eval_C, eval_X]
  have hp1 : p.coeff 1 = (14706688 : ℝ) := by
    norm_num [p, coalescedPair, nextN, nextJ, coeff_add, coeff_C_mul, coeff_X_mul, eval_add, eval_mul, eval_C, eval_X]
  have hp2 : p.coeff 2 = (26877952 : ℝ) := by
    norm_num [p, coalescedPair, nextN, nextJ, coeff_add, coeff_C_mul, coeff_X_mul, eval_add, eval_mul, eval_C, eval_X]
  have hp3 : p.coeff 3 = (14704640 : ℝ) := by
    norm_num [p, coalescedPair, nextN, nextJ, coeff_add, coeff_C_mul, coeff_X_mul, eval_add, eval_mul, eval_C, eval_X]
  have hp4 : p.coeff 4 = (2048000 : ℝ) := by
    norm_num [p, coalescedPair, nextN, nextJ, coeff_add, coeff_C_mul, coeff_X_mul, eval_add, eval_mul, eval_C, eval_X]
  have hq0 : q.coeff 0 = (1024 : ℝ) := by
    norm_num [q, coalescedPair, nextN, nextJ, coeff_add, coeff_C_mul, coeff_X_mul, eval_add, eval_mul, eval_C, eval_X]
  have hq1 : q.coeff 1 = (4169728 : ℝ) := by
    norm_num [q, coalescedPair, nextN, nextJ, coeff_add, coeff_C_mul, coeff_X_mul, eval_add, eval_mul, eval_C, eval_X]
  have hq2 : q.coeff 2 = (21299200 : ℝ) := by
    norm_num [q, coalescedPair, nextN, nextJ, coeff_add, coeff_C_mul, coeff_X_mul, eval_add, eval_mul, eval_C, eval_X]
  have hq3 : q.coeff 3 = (26034176 : ℝ) := by
    norm_num [q, coalescedPair, nextN, nextJ, coeff_add, coeff_C_mul, coeff_X_mul, eval_add, eval_mul, eval_C, eval_X]
  have hq4 : q.coeff 4 = (8437760 : ℝ) := by
    norm_num [q, coalescedPair, nextN, nextJ, coeff_add, coeff_C_mul, coeff_X_mul, eval_add, eval_mul, eval_C, eval_X]
  have hq5 : q.coeff 5 = (524288 : ℝ) := by
    norm_num [q, coalescedPair, nextN, nextJ, coeff_add, coeff_C_mul, coeff_X_mul, eval_add, eval_mul, eval_C, eval_X]
  have hpe : p.eval 8 = (18831064064 : ℝ) := by
    norm_num [p, coalescedPair, nextN, nextJ, coeff_add, coeff_C_mul, coeff_X_mul, eval_add, eval_mul, eval_C, eval_X]
  have hqe : q.eval 8 = (66466939904 : ℝ) := by
    norm_num [q, coalescedPair, nextN, nextJ, coeff_add, coeff_C_mul, coeff_X_mul, eval_add, eval_mul, eval_C, eval_X]
  have hd0 : D.coeff 0 = (77132038406144 : ℝ) := by
    change (rawD p q 8).coeff 0 = _
    rw [finiteRawD_coeff_zero p q 8 (by norm_num), hpe, hq0]
    norm_num
  have hd1 : D.coeff 1 = (244429694991073280 : ℝ) := by
    change (rawD p q 8).coeff (0+1) = _
    rw [finiteRawD_coeff_succ p q 8 (by norm_num) 0, ← hD_eq, hpe, hq1, hd0, hqe, hp0]
    norm_num
  have hd2 : D.coeff 2 = (1146145836980240384 : ℝ) := by
    change (rawD p q 8).coeff (1+1) = _
    rw [finiteRawD_coeff_succ p q 8 (by norm_num) 1, ← hD_eq, hpe, hq2, hd1, hqe, hp1]
    norm_num
  have hd3 : D.coeff 3 = (1211025563897036800 : ℝ) := by
    change (rawD p q 8).coeff (2+1) = _
    rw [finiteRawD_coeff_succ p q 8 (by norm_num) 2, ← hD_eq, hpe, hq3, hd2, hqe, hp2]
    norm_num
  have hd4 : D.coeff 4 = (298259980358778880 : ℝ) := by
    change (rawD p q 8).coeff (3+1) = _
    rw [finiteRawD_coeff_succ p q 8 (by norm_num) 3, ← hD_eq, hpe, hq4, hd3, hqe, hp3]
    norm_num
  have hd5 : D.coeff 5 = (8711954747097088 : ℝ) := by
    change (rawD p q 8).coeff (4+1) = _
    rw [finiteRawD_coeff_succ p q 8 (by norm_num) 4, ← hD_eq, hpe, hq5, hd4, hqe, hp4]
    norm_num
  constructor
  · intro i
    change D.coeff i = finiteFixedSixSite_coalescedDCoefficients i
    fin_cases i <;> norm_num [finiteFixedSixSite_coalescedDCoefficients, hd0, hd1, hd2, hd3, hd4, hd5]
  · apply coalescedFiniteState_D_positive_of_coeff_positive 5 (finiteFixedRadius 5)
    change ∀ i : Fin 6, 0 < D.coeff i
    intro i
    fin_cases i <;> norm_num [hd0, hd1, hd2, hd3, hd4, hd5]

theorem finiteFixedSixSite_coalesced_D_positive :
    ∀ i : Fin 6, 0 < (coalescedFiniteState 5 (finiteFixedRadius 5)).D i :=
  finiteFixedSixSite_coalesced_D_exact.2

end
end PhosphorylationStableCapacity
