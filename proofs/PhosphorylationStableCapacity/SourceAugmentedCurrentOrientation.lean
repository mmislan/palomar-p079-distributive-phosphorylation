module
public import proofs.PhosphorylationStableCapacity.SourceConstrainedCurrentDerivative

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section
open PhosphorylationSharpness Matrix

/-- The literal balanced-edge current derivative in all logarithmic
free-substrate coordinates, before fixing total substrate inventory. -/
def sourceCurrentLogMatrix {n : ℕ} (k : Rates n) (x : State n) :
    Matrix (Fin n) (Fin (n+1)) ℝ :=
  fun i j => k.c i * x.C i *
    ((if j = i.castSucc then 1 else 0) -
      (if j = i.succ then 1 else 0) +
      sourceLevelD x j / totalF x -
      sourceLevelC x j / totalE x)

theorem sourceCurrentLogMatrix_mulVec {n : ℕ}
    (k : Rates n) (x : State n)
    (σ : Fin (n+1) → ℝ) (i : Fin n) :
    (sourceCurrentLogMatrix k x).mulVec σ i =
      k.c i * x.C i *
        (σ i.castSucc - σ i.succ +
          (∑ j, sourceLevelD x j * σ j) / totalF x -
          (∑ j, sourceLevelC x j * σ j) / totalE x) := by
  let w := k.c i * x.C i
  have hfactor :
      (sourceCurrentLogMatrix k x).mulVec σ i =
        w * ∑ j, (((if j = i.castSucc then 1 else 0) -
          (if j = i.succ then 1 else 0) +
          sourceLevelD x j / totalF x -
          sourceLevelC x j / totalE x) * σ j) := by
    simp only [sourceCurrentLogMatrix, Matrix.mulVec, dotProduct]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [hfactor]
  congr 1
  simp_rw [sub_mul, add_mul]
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib]
  have hdelta :
      (∑ j, ((if j = i.castSucc then 1 else 0) -
        (if j = i.succ then 1 else 0)) * σ j) =
      σ i.castSucc - σ i.succ := by
    simp_rw [sub_mul]
    rw [Finset.sum_sub_distrib]
    simp
  have hD :
      (∑ j, sourceLevelD x j / totalF x * σ j) =
        (∑ j, sourceLevelD x j * σ j) / totalF x := by
    conv_lhs =>
      arg 2
      ext j
      rw [div_mul_eq_mul_div]
    rw [← Finset.sum_div]
  have hC :
      (∑ j, sourceLevelC x j / totalE x * σ j) =
        (∑ j, sourceLevelC x j * σ j) / totalE x := by
    conv_lhs =>
      arg 2
      ext j
      rw [div_mul_eq_mul_div]
    rw [← Finset.sum_div]
  rw [hdelta, hD, hC]

/-- Rows are total loaded-inventory variation and the literal
balanced-edge catalytic-current variations, in that order. -/
def sourceAugmentedCurrentMatrix {n : ℕ} (k : Rates n) (x : State n) :
    Matrix (Fin (n+1)) (Fin (n+1)) ℝ :=
  let M := (totalAndLevelOutputMatrix n) *
    loadedBindingMass x.S (sourceLevelC x) (sourceLevelD x)
      (totalE x) (totalF x)
  fun r c => Fin.cases (M 0 c) (fun i => sourceCurrentLogMatrix k x i c) r

theorem sourceAugmentedCurrentMatrix_zero {n : ℕ}
    (k : Rates n) (x : State n) (j : Fin (n+1)) :
    sourceAugmentedCurrentMatrix k x 0 j =
      ((totalAndLevelOutputMatrix n) *
        loadedBindingMass x.S (sourceLevelC x) (sourceLevelD x)
          (totalE x) (totalF x)) 0 j := rfl

theorem sourceAugmentedCurrentMatrix_succ {n : ℕ}
    (k : Rates n) (x : State n) (i : Fin n) (j : Fin (n+1)) :
    sourceAugmentedCurrentMatrix k x i.succ j =
      sourceCurrentLogMatrix k x i j := rfl

theorem sourceAugmentedCurrentMatrix_pivot_pos {n : ℕ}
    (k : Rates n) (x : State n) (hx : x.Positive) :
    0 < sourceAugmentedCurrentMatrix k x 0 0 := by
  rw [sourceAugmentedCurrentMatrix_zero]
  have h : ((totalAndLevelOutputMatrix n) *
      loadedBindingMass x.S (sourceLevelC x) (sourceLevelD x)
        (totalE x) (totalF x)) 0 0 =
      ∑ i, loadedBindingMass x.S (sourceLevelC x)
        (sourceLevelD x) (totalE x) (totalF x) i 0 := by
    simp [totalAndLevelOutputMatrix, Matrix.mul_apply]
  rw [h]
  exact source_loadedBindingMass_column_sum_pos x hx 0

theorem sourceAugmentedCurrentMatrix_mulVec_succ {n : ℕ}
    (k : Rates n) (x : State n)
    (σ : Fin (n+1) → ℝ) (i : Fin n) :
    (sourceAugmentedCurrentMatrix k x).mulVec σ i.succ =
      (sourceCurrentLogMatrix k x).mulVec σ i := by
  simp [Matrix.mulVec, dotProduct, sourceAugmentedCurrentMatrix_succ]

theorem sourceAugmentedCurrentMatrix_fixedTangent_eq {n : ℕ}
    (k : Rates n) (x : State n) (j : Fin n) :
    firstPivotFixedTangent (sourceAugmentedCurrentMatrix k x) j =
      firstPivotFixedTangent
        ((totalAndLevelOutputMatrix n) *
          loadedBindingMass x.S (sourceLevelC x) (sourceLevelD x)
            (totalE x) (totalF x)) j := by
  funext r
  simp [firstPivotFixedTangent, sourceAugmentedCurrentMatrix_zero]

theorem sourceAugmentedCurrentMatrix_schur_eq_constrained {n : ℕ}
    (k : Rates n) (x : State n) :
    (fun i j : Fin n =>
      sourceAugmentedCurrentMatrix k x i.succ j.succ -
        sourceAugmentedCurrentMatrix k x i.succ 0 /
          sourceAugmentedCurrentMatrix k x 0 0 *
          sourceAugmentedCurrentMatrix k x 0 j.succ) =
      sourceConstrainedCurrentDerivative k x := by
  funext i j
  rw [← firstPivotFixedTangent_mulVec]
  rw [sourceAugmentedCurrentMatrix_fixedTangent_eq,
    sourceAugmentedCurrentMatrix_mulVec_succ,
    sourceCurrentLogMatrix_mulVec]
  rfl

/-- The positive total-inventory pivot transfers the augmented
orientation exactly to the fixed-total catalytic-current derivative. -/
theorem sourceAugmentedCurrentMatrix_det_eq_pivot_mul_constrained {n : ℕ}
    (k : Rates n) (x : State n) (hx : x.Positive) :
    (sourceAugmentedCurrentMatrix k x).det =
      sourceAugmentedCurrentMatrix k x 0 0 *
        (sourceConstrainedCurrentDerivative k x).det := by
  rw [det_eq_first_pivot_mul_schur
    (sourceAugmentedCurrentMatrix k x)
    (ne_of_gt (sourceAugmentedCurrentMatrix_pivot_pos k x hx))]
  rw [sourceAugmentedCurrentMatrix_schur_eq_constrained]

theorem sourceAugmentedCurrentMatrix_parity_det_pos_iff {n : ℕ}
    (k : Rates n) (x : State n) (hx : x.Positive) :
    0 < (-1 : ℝ)^n * (sourceAugmentedCurrentMatrix k x).det ↔
      0 < (-1 : ℝ)^n * (sourceConstrainedCurrentDerivative k x).det := by
  rw [sourceAugmentedCurrentMatrix_det_eq_pivot_mul_constrained k x hx]
  have hp := sourceAugmentedCurrentMatrix_pivot_pos k x hx
  rw [show (-1 : ℝ)^n *
      (sourceAugmentedCurrentMatrix k x 0 0 *
        (sourceConstrainedCurrentDerivative k x).det) =
      sourceAugmentedCurrentMatrix k x 0 0 *
        ((-1 : ℝ)^n * (sourceConstrainedCurrentDerivative k x).det)
    from by ring]
  exact mul_pos_iff_of_pos_left hp

end
end PhosphorylationStableCapacity
