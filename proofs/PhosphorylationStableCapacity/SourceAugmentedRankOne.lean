module
public import proofs.PhosphorylationStableCapacity.AugmentedRankOneDeterminant
public import proofs.PhosphorylationStableCapacity.SourceAugmentedCurrentOrientation
public import proofs.PhosphorylationStableCapacity.SourceAugmentedSlopeFactor

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section
open PhosphorylationSharpness Matrix

/-- The literal total-inventory row of the physical augmented derivative. -/
def sourceAugmentedTotalRow {n : ℕ} (x : State n) :
    Fin (n+1) → ℝ :=
  fun j => ((totalAndLevelOutputMatrix n) *
    loadedBindingMass x.S (sourceLevelC x) (sourceLevelD x)
      (totalE x) (totalF x)) 0 j

/-- The positive catalytic-current factors for the non-total rows. -/
def sourceAugmentedRowWeight {n : ℕ} (k : Rates n) (x : State n) :
    Fin (n+1) → ℝ :=
  Fin.cases 1 (fun i => k.c i * x.C i)

theorem sourceAugmentedTotalRow_pos {n : ℕ}
    (x : State n) (hx : x.Positive) (j : Fin (n+1)) :
    0 < sourceAugmentedTotalRow x j := by
  have h : sourceAugmentedTotalRow x j =
      ∑ i, loadedBindingMass x.S (sourceLevelC x)
        (sourceLevelD x) (totalE x) (totalF x) i j := by
    simp [sourceAugmentedTotalRow, totalAndLevelOutputMatrix,
      Matrix.mul_apply]
  rw [h]
  exact source_loadedBindingMass_column_sum_pos x hx j

theorem sourceAugmentedTotalRow_zeroth_pos {n : ℕ}
    (x : State n) (hx : x.Positive) :
    0 < sourcePathZerothMoment (sourceAugmentedTotalRow x) := by
  unfold sourcePathZerothMoment
  exact Finset.sum_pos (fun j _ => sourceAugmentedTotalRow_pos x hx j)
    Finset.univ_nonempty

theorem sourceAugmentedRowWeight_pos {n : ℕ}
    (k : Rates n) (x : State n)
    (hk : k.Positive) (hx : x.Positive) (i : Fin (n+1)) :
    0 < sourceAugmentedRowWeight k x i := by
  cases i using Fin.cases with
  | zero => simp [sourceAugmentedRowWeight]
  | succ i =>
      simp only [sourceAugmentedRowWeight, Fin.cases_succ]
      exact mul_pos (hk i).2.2.1 (hx.2.2.2.1 i)

theorem sourceAugmentedRowWeight_prod_pos {n : ℕ}
    (k : Rates n) (x : State n)
    (hk : k.Positive) (hx : x.Positive) :
    0 < ∏ i : Fin (n+1), sourceAugmentedRowWeight k x i := by
  exact Finset.prod_pos (fun i _ => sourceAugmentedRowWeight_pos k x hk hx i)

theorem sourceAugmentedCurrentMatrix_eq_rank_one {n : ℕ}
    (k : Rates n) (x : State n) :
    sourceAugmentedCurrentMatrix k x =
      Matrix.diagonal (sourceAugmentedRowWeight k x) *
        sourceRankOneAugmented (sourceAugmentedTotalRow x)
          (sourceOccupancyDifference x) := by
  ext i j
  cases i using Fin.cases with
  | zero =>
      simp [sourceAugmentedCurrentMatrix_zero,
        sourceRankOneAugmented_first_row,
        sourceAugmentedTotalRow, sourceAugmentedRowWeight,
        Matrix.mul_apply, Matrix.diagonal_apply]
  | succ i =>
      simp [sourceAugmentedCurrentMatrix_succ,
        sourceRankOneAugmented_current_row,
        sourceCurrentLogMatrix, sourceOccupancyDifference,
        sourceAugmentedRowWeight,
        Matrix.mul_apply, Matrix.diagonal_apply]
      left
      ring

theorem sourceAugmentedCurrentMatrix_det_rank_one {n : ℕ}
    (k : Rates n) (x : State n)
    (h0 : sourcePathZerothMoment (sourceAugmentedTotalRow x) ≠ 0) :
    (sourceAugmentedCurrentMatrix k x).det =
      (∏ i : Fin (n+1), sourceAugmentedRowWeight k x i) *
        ((-1 : ℝ)^n *
          ((1 - sourcePathFirstMoment (sourceOccupancyDifference x)) *
              sourcePathZerothMoment (sourceAugmentedTotalRow x) +
            sourcePathZerothMoment (sourceOccupancyDifference x) *
              sourcePathFirstMoment (sourceAugmentedTotalRow x))) := by
  rw [sourceAugmentedCurrentMatrix_eq_rank_one, Matrix.det_mul,
    Matrix.det_diagonal, sourceRankOneAugmented_det _ _ h0]

/-- Physical orientation is the sign of one explicit scalar moment
combination; every catalytic row factor has positive sign. -/
theorem sourceAugmentedCurrentMatrix_parity_det_pos_iff_moment {n : ℕ}
    (k : Rates n) (x : State n)
    (hk : k.Positive) (hx : x.Positive) :
    0 < (-1 : ℝ)^n * (sourceAugmentedCurrentMatrix k x).det ↔
      0 < (1 - sourcePathFirstMoment (sourceOccupancyDifference x)) *
          sourcePathZerothMoment (sourceAugmentedTotalRow x) +
        sourcePathZerothMoment (sourceOccupancyDifference x) *
          sourcePathFirstMoment (sourceAugmentedTotalRow x) := by
  have h0 := ne_of_gt (sourceAugmentedTotalRow_zeroth_pos x hx)
  have hprod := sourceAugmentedRowWeight_prod_pos k x hk hx
  have hpow : (-1 : ℝ)^n * (-1 : ℝ)^n = 1 := by
    rw [← pow_add, show n + n = 2 * n by omega, pow_mul]
    norm_num
  rw [sourceAugmentedCurrentMatrix_det_rank_one k x h0]
  have heq : (-1 : ℝ)^n *
      ((∏ i : Fin (n+1), sourceAugmentedRowWeight k x i) *
        ((-1 : ℝ)^n *
          ((1 - sourcePathFirstMoment (sourceOccupancyDifference x)) *
              sourcePathZerothMoment (sourceAugmentedTotalRow x) +
            sourcePathZerothMoment (sourceOccupancyDifference x) *
              sourcePathFirstMoment (sourceAugmentedTotalRow x)))) =
      (∏ i : Fin (n+1), sourceAugmentedRowWeight k x i) *
        ((1 - sourcePathFirstMoment (sourceOccupancyDifference x)) *
            sourcePathZerothMoment (sourceAugmentedTotalRow x) +
          sourcePathZerothMoment (sourceOccupancyDifference x) *
            sourcePathFirstMoment (sourceAugmentedTotalRow x)) := by
    calc
      _ = (∏ i : Fin (n+1), sourceAugmentedRowWeight k x i) *
          (((-1 : ℝ)^n * (-1 : ℝ)^n) *
            ((1 - sourcePathFirstMoment (sourceOccupancyDifference x)) *
                sourcePathZerothMoment (sourceAugmentedTotalRow x) +
              sourcePathZerothMoment (sourceOccupancyDifference x) *
                sourcePathFirstMoment (sourceAugmentedTotalRow x))) := by ring
      _ = _ := by rw [hpow, one_mul]
  rw [heq]
  exact mul_pos_iff_of_pos_left hprod

/-- Along an affine log-substrate current-kernel direction, the
augmented determinant moment is opposite to a negative total slope
when the occupancy sum is negative. -/
theorem sourceAugmentedCurrentMatrix_parity_det_pos_of_affine_slope_neg
    {n : ℕ} (k : Rates n) (x : State n)
    (hk : k.Positive) (hx : x.Positive)
    (a b : ℝ) (hb : 0 < b)
    (hq : sourcePathZerothMoment (sourceOccupancyDifference x) < 0)
    (hkernel : a * sourcePathZerothMoment (sourceOccupancyDifference x) +
      b * (sourcePathFirstMoment (sourceOccupancyDifference x) - 1) = 0)
    (hslope : a * sourcePathZerothMoment (sourceAugmentedTotalRow x) +
      b * sourcePathFirstMoment (sourceAugmentedTotalRow x) < 0) :
    0 < (-1 : ℝ)^n * (sourceAugmentedCurrentMatrix k x).det := by
  let T0 := sourcePathZerothMoment (sourceAugmentedTotalRow x)
  let T1 := sourcePathFirstMoment (sourceAugmentedTotalRow x)
  let Q0 := sourcePathZerothMoment (sourceOccupancyDifference x)
  let Q1 := sourcePathFirstMoment (sourceOccupancyDifference x)
  have hker' : b * (1 - Q1) = a * Q0 := by
    dsimp [Q0, Q1] at hkernel ⊢
    linarith
  have hid : b * ((1 - Q1) * T0 + Q0 * T1) =
      Q0 * (a * T0 + b * T1) := by
    calc
      _ = (b * (1 - Q1)) * T0 + b * Q0 * T1 := by ring
      _ = (a * Q0) * T0 + b * Q0 * T1 := by rw [hker']
      _ = _ := by ring
  have hbracket : 0 < (1 - Q1) * T0 + Q0 * T1 := by
    have hmul : 0 < b * ((1 - Q1) * T0 + Q0 * T1) := by
      rw [hid]
      exact mul_pos_of_neg_of_neg hq hslope
    exact (mul_pos_iff_of_pos_left hb).mp hmul
  exact (sourceAugmentedCurrentMatrix_parity_det_pos_iff_moment
    k x hk hx).mpr hbracket

end
end PhosphorylationStableCapacity
