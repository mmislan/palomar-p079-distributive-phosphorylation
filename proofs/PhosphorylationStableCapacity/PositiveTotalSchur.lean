module
public import proofs.PhosphorylationStableCapacity.LoadedBindingOutputOrientation

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section
open PhosphorylationSharpness Matrix

/-- Eliminate the first column using the first row as a pivot, retaining
the first row itself. -/
def firstPivotEliminated {n : ℕ}
    (A : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) :
    Matrix (Fin (n+1)) (Fin (n+1)) ℝ :=
  fun i j => A i j - (if i = 0 then 0 else A i 0 / A 0 0) * A 0 j

/-- The all-size determinant identity for eliminating one positive
total-inventory pivot and retaining the `n × n` constrained block. -/
theorem det_eq_first_pivot_mul_schur {n : ℕ}
    (A : Matrix (Fin (n+1)) (Fin (n+1)) ℝ)
    (hp : A 0 0 ≠ 0) :
    A.det = A 0 0 *
      Matrix.det (fun i j : Fin n =>
        A i.succ j.succ - A i.succ 0 / A 0 0 * A 0 j.succ) := by
  let B := firstPivotEliminated A
  have hdet : B.det = A.det := by
    apply Matrix.det_eq_of_forall_row_eq_smul_add_const
      (fun i => if i = 0 then 0 else -(A i 0 / A 0 0)) 0
    · simp
    · intro i j
      simp [B, firstPivotEliminated]
      split_ifs <;> ring
  have hbelow (i : Fin n) : B i.succ 0 = 0 := by
    simp [B, firstPivotEliminated, hp]
  have hfirst : B 0 0 = A 0 0 := by
    simp [B, firstPivotEliminated]
  have htail : B.submatrix Fin.succ Fin.succ =
      (fun i j : Fin n =>
        A i.succ j.succ - A i.succ 0 / A 0 0 * A 0 j.succ) := by
    ext i j
    simp [B, firstPivotEliminated]
  rw [← hdet, Matrix.det_succ_column_zero]
  rw [Fin.sum_univ_succ]
  simp [hbelow, hfirst, htail]

/-- A unit variation in free-substrate level `j+1`, compensated at level
zero so the first output has zero derivative. -/
def firstPivotFixedTangent {n : ℕ}
    (A : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) (j : Fin n) :
    Fin (n+1) → ℝ :=
  fun i => if i = 0 then -(A 0 j.succ / A 0 0)
    else if i = j.succ then 1 else 0

theorem firstPivotFixedTangent_mulVec {n : ℕ}
    (A : Matrix (Fin (n+1)) (Fin (n+1)) ℝ)
    (j : Fin n) (i : Fin (n+1)) :
    A.mulVec (firstPivotFixedTangent A j) i =
      A i j.succ - A i 0 / A 0 0 * A 0 j.succ := by
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_succ,
    firstPivotFixedTangent]
  ring

theorem firstPivotFixedTangent_first_output_zero {n : ℕ}
    (A : Matrix (Fin (n+1)) (Fin (n+1)) ℝ)
    (hp : A 0 0 ≠ 0) (j : Fin n) :
    A.mulVec (firstPivotFixedTangent A j) 0 = 0 := by
  rw [firstPivotFixedTangent_mulVec]
  field_simp [hp]
  ring

/-- Binding-inventory derivative on the fixed-total substrate class,
expressed in logarithmic free-substrate coordinates `1,...,n` after
eliminating the level-zero variation. -/
def sourceConstrainedBindingMass {n : ℕ} (x : State n) :
    Matrix (Fin n) (Fin n) ℝ :=
  let A := (totalAndLevelOutputMatrix n) *
    loadedBindingMass x.S (sourceLevelC x) (sourceLevelD x)
      (totalE x) (totalF x)
  fun i j => A i.succ j.succ - A i.succ 0 / A 0 0 * A 0 j.succ

theorem sourceConstrainedBindingMass_eq_fixedTangent {n : ℕ}
    (x : State n) (i j : Fin n) :
    sourceConstrainedBindingMass x i j =
      let A := (totalAndLevelOutputMatrix n) *
        loadedBindingMass x.S (sourceLevelC x) (sourceLevelD x)
          (totalE x) (totalF x)
      A.mulVec (firstPivotFixedTangent A j) i.succ := by
  exact (firstPivotFixedTangent_mulVec _ j i.succ).symm

/-- At a positive literal equilibrium, each constrained mass entry is
the actual derivative of the corresponding loaded-level inventory along
its compensated binding path. -/
theorem equilibrium_sourceConstrainedBindingMass_hasDerivAt {n : ℕ}
    (k : Rates n) (x : State n)
    (hk : k.Positive) (hx : x.Positive)
    (heq : Equilibrium k x) (i j : Fin n) :
    let A := (totalAndLevelOutputMatrix n) *
      loadedBindingMass x.S (sourceLevelC x) (sourceLevelD x)
        (totalE x) (totalF x)
    let σ := firstPivotFixedTangent A j
    HasDerivAt (fun t : ℝ =>
      bindingLoadedLevel (totalE x) (totalF x)
        (sourceBindingP k) (sourceBindingQ k)
        (bindingLinearPath x.S σ t) i.succ)
      (sourceConstrainedBindingMass x i j) 0 := by
  dsimp only
  let M := loadedBindingMass x.S (sourceLevelC x)
    (sourceLevelD x) (totalE x) (totalF x)
  let A := (totalAndLevelOutputMatrix n) * M
  let σ := firstPivotFixedTangent A j
  have h := equilibrium_source_loadedBindingMass_hasDerivAt_kinetic
    k x hk hx heq σ i.succ
  have hderiv : M.mulVec σ i.succ =
      sourceConstrainedBindingMass x i j := by
    rw [sourceConstrainedBindingMass_eq_fixedTangent]
    change M.mulVec σ i.succ =
      ((totalAndLevelOutputMatrix n * M).mulVec σ) i.succ
    rw [← Matrix.mulVec_mulVec]
    exact (totalAndLevelOutputMatrix_mulVec_succ n (M.mulVec σ) i).symm
  rw [hderiv] at h
  exact h

theorem equilibrium_firstPivotFixedTangent_total_hasDerivAt_zero {n : ℕ}
    (k : Rates n) (x : State n)
    (hk : k.Positive) (hx : x.Positive)
    (heq : Equilibrium k x) (j : Fin n) :
    let A := (totalAndLevelOutputMatrix n) *
      loadedBindingMass x.S (sourceLevelC x) (sourceLevelD x)
        (totalE x) (totalF x)
    let σ := firstPivotFixedTangent A j
    HasDerivAt (fun t : ℝ =>
      ∑ i, bindingLoadedLevel (totalE x) (totalF x)
        (sourceBindingP k) (sourceBindingQ k)
        (bindingLinearPath x.S σ t) i) 0 0 := by
  dsimp only
  let M := loadedBindingMass x.S (sourceLevelC x)
    (sourceLevelD x) (totalE x) (totalF x)
  let A := (totalAndLevelOutputMatrix n) * M
  let σ := firstPivotFixedTangent A j
  have hsum : HasDerivAt (fun t : ℝ =>
      ∑ i, bindingLoadedLevel (totalE x) (totalF x)
        (sourceBindingP k) (sourceBindingQ k)
        (bindingLinearPath x.S σ t) i)
      (∑ i, M.mulVec σ i) 0 := by
    apply HasDerivAt.fun_sum
    intro i _
    exact equilibrium_source_loadedBindingMass_hasDerivAt_kinetic
      k x hk hx heq σ i
  have hp : 0 < A 0 0 := by
    have h : A 0 0 = ∑ i, M i 0 := by
      simp [A, M, totalAndLevelOutputMatrix, Matrix.mul_apply]
    rw [h]
    exact source_loadedBindingMass_column_sum_pos x hx 0
  have hzero : (∑ i, M.mulVec σ i) = 0 := by
    have h := firstPivotFixedTangent_first_output_zero A (ne_of_gt hp) j
    change ((totalAndLevelOutputMatrix n * M).mulVec σ) 0 = 0 at h
    rw [← Matrix.mulVec_mulVec,
      totalAndLevelOutputMatrix_mulVec_zero] at h
    exact h
  rw [hzero] at hsum
  exact hsum

/-- The actual fixed-total binding coordinate change preserves positive
orientation for every positive literal state. -/
theorem sourceConstrainedBindingMass_det_pos {n : ℕ}
    (x : State n) (hx : x.Positive) :
    0 < (sourceConstrainedBindingMass x).det := by
  let M := loadedBindingMass x.S (sourceLevelC x)
    (sourceLevelD x) (totalE x) (totalF x)
  let A := (totalAndLevelOutputMatrix n) * M
  have hp : 0 < A 0 0 := by
    have h : A 0 0 = ∑ i, M i 0 := by
      simp [A, M, totalAndLevelOutputMatrix, Matrix.mul_apply]
    rw [h]
    exact source_loadedBindingMass_column_sum_pos x hx 0
  have hfactor := det_eq_first_pivot_mul_schur A (ne_of_gt hp)
  have hfull : 0 < A.det :=
    source_totalAndLevel_bindingMass_det_pos x hx
  rw [hfactor] at hfull
  exact (mul_pos_iff_of_pos_left hp).mp hfull

end
end PhosphorylationStableCapacity
