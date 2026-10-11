module
public import Mathlib.Basic.Real.Basic
public import Mathlib.LinearAlgebra.Matrix.Block
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.Data.Fintype.Fin
public import Mathlib.Tactic.Ring
public import Lean.Elab.Tactic.Omega

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section
open Matrix

/-- Columns of this unit lower-triangular matrix encode a common scale
direction followed by successive cumulative differences. -/
def sourceCumulativeMatrix (n : ℕ) :
    Matrix (Fin (n+1)) (Fin (n+1)) ℝ :=
  fun i j => if j ≤ i then 1 else 0

theorem sourceCumulativeMatrix_lowerTriangular (n : ℕ) :
    (sourceCumulativeMatrix n).BlockTriangular
      (OrderDual.toDual : Fin (n+1) → OrderDual (Fin (n+1))) := by
  intro i j hji
  have hij : i < j := hji
  simp [sourceCumulativeMatrix, not_le.mpr hij]

-- The two branches use the lemma names in mathlib 4.35 and 4.30,
-- respectively. Each pinned linter sees the other branch as unused.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
theorem sourceCumulativeMatrix_det (n : ℕ) :
    (sourceCumulativeMatrix n).det = 1 := by
  first
  | rw [Matrix.det_of_isLowerTriangular _
      (sourceCumulativeMatrix_lowerTriangular n)]
  | rw [Matrix.det_of_lowerTriangular _
      (sourceCumulativeMatrix_lowerTriangular n)]
  simp [sourceCumulativeMatrix]

/-- A total-inventory row over the incidence differences of one path. -/
def sourceDifferenceAugmented {n : ℕ} (t : Fin (n+1) → ℝ) :
    Matrix (Fin (n+1)) (Fin (n+1)) ℝ :=
  fun i j => Fin.cases (t j)
    (fun e => (if j = e.castSucc then 1 else 0) -
      (if j = e.succ then 1 else 0)) i

theorem sourceDifferenceAugmented_mul_cumulative_succ {n : ℕ}
    (t : Fin (n+1) → ℝ) (i : Fin n) (k : Fin (n+1)) :
    (sourceDifferenceAugmented t * sourceCumulativeMatrix n)
      i.succ k =
      sourceCumulativeMatrix n i.castSucc k -
        sourceCumulativeMatrix n i.succ k := by
  simp [Matrix.mul_apply, sourceDifferenceAugmented,
    Finset.sum_sub_distrib, sub_mul]

theorem sourceDifferenceAugmented_mul_cumulative_zero {n : ℕ}
    (t : Fin (n+1) → ℝ) :
    (sourceDifferenceAugmented t * sourceCumulativeMatrix n) 0 0 =
      ∑ j, t j := by
  simp [Matrix.mul_apply, sourceDifferenceAugmented,
    sourceCumulativeMatrix]

theorem sourceDifferenceAugmented_mul_cumulative_succ_zero {n : ℕ}
    (t : Fin (n+1) → ℝ) (i : Fin n) :
    (sourceDifferenceAugmented t * sourceCumulativeMatrix n)
      i.succ 0 = 0 := by
  rw [sourceDifferenceAugmented_mul_cumulative_succ]
  simp [sourceCumulativeMatrix]

theorem sourceDifferenceAugmented_mul_cumulative_succ_succ {n : ℕ}
    (t : Fin (n+1) → ℝ) (i j : Fin n) :
    (sourceDifferenceAugmented t * sourceCumulativeMatrix n)
      i.succ j.succ = if i = j then -1 else 0 := by
  rw [sourceDifferenceAugmented_mul_cumulative_succ]
  have hfirst : (j.succ ≤ i.castSucc) ↔ j < i := by
    simp only [Fin.le_iff_val_le_val, Fin.lt_def,
      Fin.val_succ, Fin.val_castSucc]
    omega
  have hsecond : (j.succ ≤ i.succ) ↔ j ≤ i := by
    simp only [Fin.le_iff_val_le_val, Fin.val_succ]
    omega
  simp only [sourceCumulativeMatrix, hfirst, hsecond]
  rcases lt_trichotomy j i with hlt | heq | hgt
  · simp [hlt, hlt.le, ne_of_gt hlt]
  · subst j
    simp
  · have hnle : ¬ j ≤ i := not_le.mpr hgt
    have hnlt : ¬ j < i := not_lt.mpr hgt.le
    simp [hnle, hnlt, ne_of_lt hgt]

/-- The path-difference block contributes `(-1)^n`; the first row
contributes the sum of its entries. -/
theorem sourceDifferenceAugmented_det {n : ℕ}
    (t : Fin (n+1) → ℝ) :
    (sourceDifferenceAugmented t).det =
      (-1 : ℝ)^n * ∑ j, t j := by
  let A := sourceDifferenceAugmented t * sourceCumulativeMatrix n
  have hdet : A.det = (sourceDifferenceAugmented t).det := by
    simp [A, Matrix.det_mul, sourceCumulativeMatrix_det]
  have hbelow (i : Fin n) : A i.succ 0 = 0 :=
    sourceDifferenceAugmented_mul_cumulative_succ_zero t i
  have hfirst : A 0 0 = ∑ j, t j :=
    sourceDifferenceAugmented_mul_cumulative_zero t
  have hminor : A.submatrix Fin.succ Fin.succ =
      -(1 : Matrix (Fin n) (Fin n) ℝ) := by
    ext i j
    rw [Matrix.submatrix_apply]
    change (sourceDifferenceAugmented t * sourceCumulativeMatrix n)
      i.succ j.succ = _
    rw [sourceDifferenceAugmented_mul_cumulative_succ_succ]
    by_cases hij : i = j <;> simp [hij]
  rw [← hdet, Matrix.det_succ_column_zero, Fin.sum_univ_succ]
  simp [hbelow, hfirst, hminor, Matrix.det_neg,
    Fintype.card_fin]
  ring

def sourcePathZerothMoment {n : ℕ} (t : Fin (n+1) → ℝ) : ℝ :=
  ∑ j, t j

def sourcePathFirstMoment {n : ℕ} (t : Fin (n+1) → ℝ) : ℝ :=
  ∑ j, (j.val : ℝ) * t j

def sourcePathUnitVector {n : ℕ} : Fin (n+1) → ℝ :=
  fun i => if i = 0 then 0 else 1

/-- The path-difference rows act by neighboring subtraction. -/
theorem sourceDifferenceAugmented_mulVec_succ {n : ℕ}
    (t y : Fin (n+1) → ℝ) (i : Fin n) :
    (sourceDifferenceAugmented t).mulVec y i.succ =
      y i.castSucc - y i.succ := by
  simp [Matrix.mulVec, dotProduct, sourceDifferenceAugmented,
    Finset.sum_sub_distrib, sub_mul]

theorem sourceDifferenceAugmented_mulVec_zero {n : ℕ}
    (t y : Fin (n+1) → ℝ) :
    (sourceDifferenceAugmented t).mulVec y 0 =
      ∑ j, t j * y j := by
  simp [Matrix.mulVec, dotProduct, sourceDifferenceAugmented]

/-- Explicit solution of the base difference system with zero total
row and unit current rows. -/
def sourceDifferenceSolution {n : ℕ}
    (t : Fin (n+1) → ℝ) : Fin (n+1) → ℝ :=
  fun j => sourcePathFirstMoment t / sourcePathZerothMoment t - j.val

theorem sourceDifferenceAugmented_solution {n : ℕ}
    (t : Fin (n+1) → ℝ)
    (h0 : sourcePathZerothMoment t ≠ 0) :
    (sourceDifferenceAugmented t).mulVec
      (sourceDifferenceSolution t) = sourcePathUnitVector := by
  funext i
  cases i using Fin.cases with
  | zero =>
      rw [sourceDifferenceAugmented_mulVec_zero]
      simp only [sourceDifferenceSolution, sourcePathUnitVector,
        ite_true, sourcePathZerothMoment, sourcePathFirstMoment]
      have hsum :
          (∑ j : Fin (n+1), t j *
            ((∑ l : Fin (n+1), (l.val : ℝ) * t l) /
              (∑ l : Fin (n+1), t l) - j.val)) =
          (∑ j, t j) *
              ((∑ l : Fin (n+1), (l.val : ℝ) * t l) /
                (∑ l : Fin (n+1), t l)) -
            (∑ j, (j.val : ℝ) * t j) := by
        simp only [mul_sub, Finset.sum_sub_distrib,
          ← Finset.sum_mul]
        congr 1
        apply Finset.sum_congr rfl
        intro j _
        ring
      rw [hsum]
      have h0' : (∑ j, t j) ≠ 0 := h0
      rw [mul_comm (∑ j, t j)
        ((∑ l : Fin (n+1), (l.val : ℝ) * t l) / (∑ l, t l)),
        div_mul_cancel₀ _ h0']
      ring
  | succ i =>
      rw [sourceDifferenceAugmented_mulVec_succ]
      simp [sourceDifferenceSolution, sourcePathUnitVector]

end
end PhosphorylationStableCapacity
