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

def finiteFixedSevenSite_DCoefficients : Fin 7 → ℝ :=
  ![(6133946663909515512686625 : ℝ) / 1073741824, (42432394031126878285313977275 : ℝ) / 134217728, (4883680848451184948583934785 : ℝ) / 2097152, (599459962547493940208844675 : ℝ) / 131072, (2809832322127825131906055 : ℝ) / 1024, (3434747575909172672345 : ℝ) / 8, (8140728199178708560 : ℝ)]
def finiteFixedSevenSite_BCoefficients : Fin 7 → ℝ :=
  ![(1358755686159373888354995901875 : ℝ) / 1073741824, (3812416726363947537790248149625 : ℝ) / 268435456, (25773011302131208501646007825 : ℝ) / 524288, (16215630162548563384018278975 : ℝ) / 262144, (27251573224440190586550975 : ℝ) / 1024, (46385318223323424350775 : ℝ) / 16, (2163242300484434400 : ℝ)]

/-- Exact coefficient lookup and positivity for the printed n=7 family. -/
theorem finiteFixedSevenSite_coefficients_exact :
    (∀ i : Fin 7, (arbitrarySplitRawD 6 (finiteFixedOffset 6)
      (finiteFixedRadius 6) (finiteFixedSpacing 6)).coeff i = finiteFixedSevenSite_DCoefficients i) ∧
    (∀ i : Fin 7, (arbitrarySplitRawB 6 (finiteFixedOffset 6)
      (finiteFixedRadius 6) (finiteFixedSpacing 6)).coeff i = finiteFixedSevenSite_BCoefficients i) ∧
    DensePositive
      (arbitrarySplitRawD 6 (finiteFixedOffset 6)
        (finiteFixedRadius 6) (finiteFixedSpacing 6)) 6 ∧
    DensePositive
      (arbitrarySplitRawB 6 (finiteFixedOffset 6)
        (finiteFixedRadius 6) (finiteFixedSpacing 6)) 6 := by
  let p := (arbitrarySplitPair 6 (finiteFixedOffset 6)
    (finiteFixedSpacing 6)).1
  let q := (arbitrarySplitPair 6 (finiteFixedOffset 6)
    (finiteFixedSpacing 6)).2
  let D := arbitrarySplitRawD 6 (finiteFixedOffset 6)
    (finiteFixedRadius 6) (finiteFixedSpacing 6)
  let B := arbitrarySplitRawB 6 (finiteFixedOffset 6)
    (finiteFixedRadius 6) (finiteFixedSpacing 6)
  have hD_eq : D = rawD p q 8 := rfl
  have hp0 : p.coeff 0 = (1512381595725 : ℝ) / 65536 := by
    norm_num [p, arbitrarySplitPair, offsetSplitRoot, finiteFixedOffset, finiteFixedSpacing, nextN, nextJ, coeff_add, coeff_C_mul, coeff_X_mul, eval_add, eval_mul, eval_C, eval_X]
  have hp1 : p.coeff 1 = (1850951283615 : ℝ) / 8192 := by
    norm_num [p, arbitrarySplitPair, offsetSplitRoot, finiteFixedOffset, finiteFixedSpacing, nextN, nextJ, coeff_add, coeff_C_mul, coeff_X_mul, eval_add, eval_mul, eval_C, eval_X]
  have hp2 : p.coeff 2 = (84311813421 : ℝ) / 128 := by
    norm_num [p, arbitrarySplitPair, offsetSplitRoot, finiteFixedOffset, finiteFixedSpacing, nextN, nextJ, coeff_add, coeff_C_mul, coeff_X_mul, eval_add, eval_mul, eval_C, eval_X]
  have hp3 : p.coeff 3 = (5448317895 : ℝ) / 8 := by
    norm_num [p, arbitrarySplitPair, offsetSplitRoot, finiteFixedOffset, finiteFixedSpacing, nextN, nextJ, coeff_add, coeff_C_mul, coeff_X_mul, eval_add, eval_mul, eval_C, eval_X]
  have hp4 : p.coeff 4 = (240058288 : ℝ) := by
    norm_num [p, arbitrarySplitPair, offsetSplitRoot, finiteFixedOffset, finiteFixedSpacing, nextN, nextJ, coeff_add, coeff_C_mul, coeff_X_mul, eval_add, eval_mul, eval_C, eval_X]
  have hp5 : p.coeff 5 = (23013376 : ℝ) := by
    norm_num [p, arbitrarySplitPair, offsetSplitRoot, finiteFixedOffset, finiteFixedSpacing, nextN, nextJ, coeff_add, coeff_C_mul, coeff_X_mul, eval_add, eval_mul, eval_C, eval_X]
  have hp6 : p.coeff 6 = (262144 : ℝ) := by
    norm_num [p, arbitrarySplitPair, offsetSplitRoot, finiteFixedOffset, finiteFixedSpacing, nextN, nextJ, coeff_add, coeff_C_mul, coeff_X_mul, eval_add, eval_mul, eval_C, eval_X]
  have hq0 : q.coeff 0 = (42567525 : ℝ) / 65536 := by
    norm_num [q, arbitrarySplitPair, offsetSplitRoot, finiteFixedOffset, finiteFixedSpacing, nextN, nextJ, coeff_add, coeff_C_mul, coeff_X_mul, eval_add, eval_mul, eval_C, eval_X]
  have hq1 : q.coeff 1 = (94475928015 : ℝ) / 2048 := by
    norm_num [q, arbitrarySplitPair, offsetSplitRoot, finiteFixedOffset, finiteFixedSpacing, nextN, nextJ, coeff_add, coeff_C_mul, coeff_X_mul, eval_add, eval_mul, eval_C, eval_X]
  have hq2 : q.coeff 2 = (46080556299 : ℝ) / 128 := by
    norm_num [q, arbitrarySplitPair, offsetSplitRoot, finiteFixedOffset, finiteFixedSpacing, nextN, nextJ, coeff_add, coeff_C_mul, coeff_X_mul, eval_add, eval_mul, eval_C, eval_X]
  have hq3 : q.coeff 3 = (3110505315 : ℝ) / 4 := by
    norm_num [q, arbitrarySplitPair, offsetSplitRoot, finiteFixedOffset, finiteFixedSpacing, nextN, nextJ, coeff_add, coeff_C_mul, coeff_X_mul, eval_add, eval_mul, eval_C, eval_X]
  have hq4 : q.coeff 4 = (547570672 : ℝ) := by
    norm_num [q, arbitrarySplitPair, offsetSplitRoot, finiteFixedOffset, finiteFixedSpacing, nextN, nextJ, coeff_add, coeff_C_mul, coeff_X_mul, eval_add, eval_mul, eval_C, eval_X]
  have hq5 : q.coeff 5 = (115769344 : ℝ) := by
    norm_num [q, arbitrarySplitPair, offsetSplitRoot, finiteFixedOffset, finiteFixedSpacing, nextN, nextJ, coeff_add, coeff_C_mul, coeff_X_mul, eval_add, eval_mul, eval_C, eval_X]
  have hq6 : q.coeff 6 = (4980736 : ℝ) := by
    norm_num [q, arbitrarySplitPair, offsetSplitRoot, finiteFixedOffset, finiteFixedSpacing, nextN, nextJ, coeff_add, coeff_C_mul, coeff_X_mul, eval_add, eval_mul, eval_C, eval_X]
  have hpe : p.eval 8 = (144099208584701965 : ℝ) / 65536 := by
    norm_num [p, arbitrarySplitPair, offsetSplitRoot, finiteFixedOffset, finiteFixedSpacing, nextN, nextJ, coeff_add, coeff_C_mul, coeff_X_mul, eval_add, eval_mul, eval_C, eval_X]
  have hqe : q.eval 8 = (508795512448669285 : ℝ) / 65536 := by
    norm_num [q, arbitrarySplitPair, offsetSplitRoot, finiteFixedOffset, finiteFixedSpacing, nextN, nextJ, coeff_add, coeff_C_mul, coeff_X_mul, eval_add, eval_mul, eval_C, eval_X]
  have hd0 : D.coeff 0 = (6133946663909515512686625 : ℝ) / 1073741824 := by
    change (rawD p q 8).coeff 0 = _
    rw [finiteRawD_coeff_zero p q 8 (by norm_num), hpe, hq0]
    norm_num
  have hd1 : D.coeff 1 = (42432394031126878285313977275 : ℝ) / 134217728 := by
    change (rawD p q 8).coeff (0 + 1) = _
    rw [finiteRawD_coeff_succ p q 8 (by norm_num) 0,
      ← hD_eq, hpe, hq1, hd0, hqe, hp0]
    norm_num
  have hd2 : D.coeff 2 = (4883680848451184948583934785 : ℝ) / 2097152 := by
    change (rawD p q 8).coeff (1 + 1) = _
    rw [finiteRawD_coeff_succ p q 8 (by norm_num) 1,
      ← hD_eq, hpe, hq2, hd1, hqe, hp1]
    norm_num
  have hd3 : D.coeff 3 = (599459962547493940208844675 : ℝ) / 131072 := by
    change (rawD p q 8).coeff (2 + 1) = _
    rw [finiteRawD_coeff_succ p q 8 (by norm_num) 2,
      ← hD_eq, hpe, hq3, hd2, hqe, hp2]
    norm_num
  have hd4 : D.coeff 4 = (2809832322127825131906055 : ℝ) / 1024 := by
    change (rawD p q 8).coeff (3 + 1) = _
    rw [finiteRawD_coeff_succ p q 8 (by norm_num) 3,
      ← hD_eq, hpe, hq4, hd3, hqe, hp3]
    norm_num
  have hd5 : D.coeff 5 = (3434747575909172672345 : ℝ) / 8 := by
    change (rawD p q 8).coeff (4 + 1) = _
    rw [finiteRawD_coeff_succ p q 8 (by norm_num) 4,
      ← hD_eq, hpe, hq5, hd4, hqe, hp4]
    norm_num
  have hd6 : D.coeff 6 = (8140728199178708560 : ℝ) := by
    change (rawD p q 8).coeff (5 + 1) = _
    rw [finiteRawD_coeff_succ p q 8 (by norm_num) 5,
      ← hD_eq, hpe, hq6, hd5, hqe, hp5]
    norm_num
  have hb0 : B.coeff 0 = (1358755686159373888354995901875 : ℝ) / 1073741824 := by
    change (rawB p q 8).coeff 0 = _
    rw [finiteRawB_coeff p q 8 0, ← hD_eq, hd0, hpe, hqe, hp0, hq0]
    norm_num
  have hb1 : B.coeff 1 = (3812416726363947537790248149625 : ℝ) / 268435456 := by
    change (rawB p q 8).coeff 1 = _
    rw [finiteRawB_coeff p q 8 1, ← hD_eq, hd1, hpe, hqe, hp1, hq1]
    norm_num
  have hb2 : B.coeff 2 = (25773011302131208501646007825 : ℝ) / 524288 := by
    change (rawB p q 8).coeff 2 = _
    rw [finiteRawB_coeff p q 8 2, ← hD_eq, hd2, hpe, hqe, hp2, hq2]
    norm_num
  have hb3 : B.coeff 3 = (16215630162548563384018278975 : ℝ) / 262144 := by
    change (rawB p q 8).coeff 3 = _
    rw [finiteRawB_coeff p q 8 3, ← hD_eq, hd3, hpe, hqe, hp3, hq3]
    norm_num
  have hb4 : B.coeff 4 = (27251573224440190586550975 : ℝ) / 1024 := by
    change (rawB p q 8).coeff 4 = _
    rw [finiteRawB_coeff p q 8 4, ← hD_eq, hd4, hpe, hqe, hp4, hq4]
    norm_num
  have hb5 : B.coeff 5 = (46385318223323424350775 : ℝ) / 16 := by
    change (rawB p q 8).coeff 5 = _
    rw [finiteRawB_coeff p q 8 5, ← hD_eq, hd5, hpe, hqe, hp5, hq5]
    norm_num
  have hb6 : B.coeff 6 = (2163242300484434400 : ℝ) := by
    change (rawB p q 8).coeff 6 = _
    rw [finiteRawB_coeff p q 8 6, ← hD_eq, hd6, hpe, hqe, hp6, hq6]
    norm_num
  refine ⟨?_, ?_, ?_⟩
  · intro i
    change D.coeff i = finiteFixedSevenSite_DCoefficients i
    fin_cases i <;> norm_num [finiteFixedSevenSite_DCoefficients, hd0, hd1, hd2, hd3, hd4, hd5, hd6]
  · intro i
    change B.coeff i = finiteFixedSevenSite_BCoefficients i
    fin_cases i <;> norm_num [finiteFixedSevenSite_BCoefficients, hb0, hb1, hb2, hb3, hb4, hb5, hb6]
  · apply finiteFixed_raw_dense_of_coeff_positive 6
    · intro j hj
      exact finiteFixed_root_gt_one_of_range 6 (by omega) (by omega) j
    · change ∀ i : Fin 7, 0 < D.coeff i
      intro i
      fin_cases i <;> norm_num [hd0, hd1, hd2, hd3, hd4, hd5, hd6]
    · change ∀ i : Fin 7, 0 < B.coeff i
      intro i
      fin_cases i <;> norm_num [hb0, hb1, hb2, hb3, hb4, hb5, hb6]

theorem finiteFixedSevenSite_coefficients_positive :
    DensePositive (arbitrarySplitRawD 6 (finiteFixedOffset 6)
      (finiteFixedRadius 6) (finiteFixedSpacing 6)) 6 ∧
    DensePositive (arbitrarySplitRawB 6 (finiteFixedOffset 6)
      (finiteFixedRadius 6) (finiteFixedSpacing 6)) 6 :=
  finiteFixedSevenSite_coefficients_exact.2.2

def finiteFixedSevenSite_coalescedDCoefficients : Fin 7 → ℝ :=
  ![(37750184410611712 : ℝ), (480975438774068576256 : ℝ), (3176880708511579766784 : ℝ), (5604965789423959539712 : ℝ), (3081324259733353267200 : ℝ), (455959198799971221504 : ℝ), (8530497334159605760 : ℝ)]

theorem finiteFixedSevenSite_coalesced_D_exact :
    (∀ i : Fin 7, (coalescedRawD 6 (finiteFixedRadius 6)).coeff i =
      finiteFixedSevenSite_coalescedDCoefficients i) ∧
    (∀ i : Fin 7, 0 < (coalescedFiniteState 6 (finiteFixedRadius 6)).D i) := by
  let p := (coalescedPair 6).1
  let q := (coalescedPair 6).2
  let D := coalescedRawD 6 (finiteFixedRadius 6)
  have hD_eq : D = rawD p q 8 := rfl
  have hp0 : p.coeff 0 = (33550336 : ℝ) := by
    norm_num [p, coalescedPair, nextN, nextJ, coeff_add, coeff_C_mul, coeff_X_mul, eval_add, eval_mul, eval_C, eval_X]
  have hp1 : p.coeff 1 = (302112768 : ℝ) := by
    norm_num [p, coalescedPair, nextN, nextJ, coeff_add, coeff_C_mul, coeff_X_mul, eval_add, eval_mul, eval_C, eval_X]
  have hp2 : p.coeff 2 = (803291136 : ℝ) := by
    norm_num [p, coalescedPair, nextN, nextJ, coeff_add, coeff_C_mul, coeff_X_mul, eval_add, eval_mul, eval_C, eval_X]
  have hp3 : p.coeff 3 = (762707968 : ℝ) := by
    norm_num [p, coalescedPair, nextN, nextJ, coeff_add, coeff_C_mul, coeff_X_mul, eval_add, eval_mul, eval_C, eval_X]
  have hp4 : p.coeff 4 = (251658240 : ℝ) := by
    norm_num [p, coalescedPair, nextN, nextJ, coeff_add, coeff_C_mul, coeff_X_mul, eval_add, eval_mul, eval_C, eval_X]
  have hp5 : p.coeff 5 = (23199744 : ℝ) := by
    norm_num [p, coalescedPair, nextN, nextJ, coeff_add, coeff_C_mul, coeff_X_mul, eval_add, eval_mul, eval_C, eval_X]
  have hq0 : q.coeff 0 = (4096 : ℝ) := by
    norm_num [q, coalescedPair, nextN, nextJ, coeff_add, coeff_C_mul, coeff_X_mul, eval_add, eval_mul, eval_C, eval_X]
  have hq1 : q.coeff 1 = (66994176 : ℝ) := by
    norm_num [q, coalescedPair, nextN, nextJ, coeff_add, coeff_C_mul, coeff_X_mul, eval_add, eval_mul, eval_C, eval_X]
  have hq2 : q.coeff 2 = (471515136 : ℝ) := by
    norm_num [q, coalescedPair, nextN, nextJ, coeff_add, coeff_C_mul, coeff_X_mul, eval_add, eval_mul, eval_C, eval_X]
  have hq3 : q.coeff 3 = (919601152 : ℝ) := by
    norm_num [q, coalescedPair, nextN, nextJ, coeff_add, coeff_C_mul, coeff_X_mul, eval_add, eval_mul, eval_C, eval_X]
  have hq4 : q.coeff 4 = (594935808 : ℝ) := by
    norm_num [q, coalescedPair, nextN, nextJ, coeff_add, coeff_C_mul, coeff_X_mul, eval_add, eval_mul, eval_C, eval_X]
  have hq5 : q.coeff 5 = (118751232 : ℝ) := by
    norm_num [q, coalescedPair, nextN, nextJ, coeff_add, coeff_C_mul, coeff_X_mul, eval_add, eval_mul, eval_C, eval_X]
  have hq6 : q.coeff 6 = (4980736 : ℝ) := by
    norm_num [q, coalescedPair, nextN, nextJ, coeff_add, coeff_C_mul, coeff_X_mul, eval_add, eval_mul, eval_C, eval_X]
  have hpe : p.eval 8 = (2304088403968 : ℝ) := by
    norm_num [p, coalescedPair, nextN, nextJ, coeff_add, coeff_C_mul, coeff_X_mul, eval_add, eval_mul, eval_C, eval_X]
  have hqe : q.eval 8 = (8135316213760 : ℝ) := by
    norm_num [q, coalescedPair, nextN, nextJ, coeff_add, coeff_C_mul, coeff_X_mul, eval_add, eval_mul, eval_C, eval_X]
  have hd0 : D.coeff 0 = (37750184410611712 : ℝ) := by
    change (rawD p q 8).coeff 0 = _
    rw [finiteRawD_coeff_zero p q 8 (by norm_num), hpe, hq0]
    norm_num
  have hd1 : D.coeff 1 = (480975438774068576256 : ℝ) := by
    change (rawD p q 8).coeff (0+1) = _
    rw [finiteRawD_coeff_succ p q 8 (by norm_num) 0, ← hD_eq, hpe, hq1, hd0, hqe, hp0]
    norm_num
  have hd2 : D.coeff 2 = (3176880708511579766784 : ℝ) := by
    change (rawD p q 8).coeff (1+1) = _
    rw [finiteRawD_coeff_succ p q 8 (by norm_num) 1, ← hD_eq, hpe, hq2, hd1, hqe, hp1]
    norm_num
  have hd3 : D.coeff 3 = (5604965789423959539712 : ℝ) := by
    change (rawD p q 8).coeff (2+1) = _
    rw [finiteRawD_coeff_succ p q 8 (by norm_num) 2, ← hD_eq, hpe, hq3, hd2, hqe, hp2]
    norm_num
  have hd4 : D.coeff 4 = (3081324259733353267200 : ℝ) := by
    change (rawD p q 8).coeff (3+1) = _
    rw [finiteRawD_coeff_succ p q 8 (by norm_num) 3, ← hD_eq, hpe, hq4, hd3, hqe, hp3]
    norm_num
  have hd5 : D.coeff 5 = (455959198799971221504 : ℝ) := by
    change (rawD p q 8).coeff (4+1) = _
    rw [finiteRawD_coeff_succ p q 8 (by norm_num) 4, ← hD_eq, hpe, hq5, hd4, hqe, hp4]
    norm_num
  have hd6 : D.coeff 6 = (8530497334159605760 : ℝ) := by
    change (rawD p q 8).coeff (5+1) = _
    rw [finiteRawD_coeff_succ p q 8 (by norm_num) 5, ← hD_eq, hpe, hq6, hd5, hqe, hp5]
    norm_num
  constructor
  · intro i
    change D.coeff i = finiteFixedSevenSite_coalescedDCoefficients i
    fin_cases i <;> norm_num [finiteFixedSevenSite_coalescedDCoefficients, hd0, hd1, hd2, hd3, hd4, hd5, hd6]
  · apply coalescedFiniteState_D_positive_of_coeff_positive 6 (finiteFixedRadius 6)
    change ∀ i : Fin 7, 0 < D.coeff i
    intro i
    fin_cases i <;> norm_num [hd0, hd1, hd2, hd3, hd4, hd5, hd6]

theorem finiteFixedSevenSite_coalesced_D_positive :
    ∀ i : Fin 7, 0 < (coalescedFiniteState 6 (finiteFixedRadius 6)).D i :=
  finiteFixedSevenSite_coalesced_D_exact.2

end
end PhosphorylationStableCapacity
