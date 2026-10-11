module
public import Mathlib.Analysis.Calculus.FDeriv.Add
public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Lean.Elab.Tactic.Omega
public import proofs.PhosphorylationSharpness.Source
public import Mathlib.LinearAlgebra.Matrix.Block

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section
open PhosphorylationSharpness

/-- Selecting the incoming substrate in the finite path is the same as
discarding level zero and taking the preceding free-substrate coordinate. -/
theorem source_previous_substrate_sum {n : ℕ} (v : Fin n → ℝ) (i : Fin n) :
    (∑ j : Fin n, if j.succ = i.castSucc then v j else 0) =
      Fin.cases 0 v i.castSucc := by
  by_cases hi : i.val = 0
  · let z : Fin n := ⟨0, by omega⟩
    have hzero : i = z := Fin.ext (by simpa [z] using hi)
    rw [hzero]
    simp [z]
  · let j : Fin n := ⟨i.val-1, by omega⟩
    have hj : j.succ = i.castSucc := Fin.ext (by simp [j]; omega)
    have huniq (k : Fin n) : k.succ = i.castSucc ↔ k = j := by
      constructor
      · intro h
        apply Fin.succ_injective
        rw [h, hj]
      · intro h
        rw [h]
        exact hj
    simp only [huniq]
    simp [← hj]

theorem source_free_substrate_split {n : ℕ}
    (S0 : ℝ) (s : Fin n → ℝ) (j : Fin (n+1)) :
    (Fin.cases S0 s : Fin (n+1) → ℝ) j =
      (Fin.cases (0 : ℝ) s : Fin (n+1) → ℝ) j +
      (Fin.cases S0 (0 : Fin n → ℝ) : Fin (n+1) → ℝ) j := by
  cases j using Fin.cases with
  | zero => simp
  | succ j => simp

/-- Catalytic current after exact complex balance, with free substrate
coordinates `S₁,...,Sₙ` and `S₀,E,F` held separately. -/
def sourceBindingCurrentAtFree {n : ℕ}
    (k : Rates n) (p q : Fin (n+1) → ℝ)
    (S0 E F : ℝ) (s : Fin n → ℝ) (i : Fin n) : ℝ :=
  k.c i * p i.castSucc * E * (Fin.cases S0 s i.castSucc) -
    k.gamma i * q i.succ * F * s i

/-- The derivative of the catalytic-current equations with respect to
`S₁,...,Sₙ`, holding `S₀`, `E`, and `F` fixed after complex balance. -/
def sourceBindingCurrentSubstrateJacobian {n : ℕ}
    (k : Rates n) (p q : Fin (n+1) → ℝ) (E F : ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  fun i j =>
    (if j.succ = i.castSucc then k.c i * p i.castSucc * E else 0) -
    (if j = i then k.gamma i * q i.succ * F else 0)

theorem sourceBindingCurrentAtFree_affine {n : ℕ}
    (k : Rates n) (p q : Fin (n+1) → ℝ)
    (S0 E F : ℝ) (s : Fin n → ℝ) :
    sourceBindingCurrentAtFree k p q S0 E F s =
      (sourceBindingCurrentSubstrateJacobian k p q E F).mulVec s +
        sourceBindingCurrentAtFree k p q S0 E F 0 := by
  funext i
  simp only [Pi.add_apply]
  unfold sourceBindingCurrentAtFree
  have hsplit : (Fin.cases S0 s : Fin (n+1) → ℝ) i.castSucc =
      (Fin.cases (0 : ℝ) s : Fin (n+1) → ℝ) i.castSucc +
        (Fin.cases S0 (0 : Fin n → ℝ) : Fin (n+1) → ℝ) i.castSucc := by
    simpa only using source_free_substrate_split S0 s i.castSucc
  have hsplit' : (Fin.cases S0 s i.castSucc : ℝ) =
      (Fin.cases (0 : ℝ) s i.castSucc : ℝ) +
        (Fin.cases S0 (0 : Fin n → ℝ) i.castSucc : ℝ) := hsplit
  rw [hsplit']
  simp [sourceBindingCurrentSubstrateJacobian, Matrix.mulVec, dotProduct,
    Finset.sum_sub_distrib, sub_mul, source_previous_substrate_sum]
  have hmul : Fin.cases (0 : ℝ)
      (fun j : Fin n => k.c i * p i.castSucc * E * s j) i.castSucc =
      k.c i * p i.castSucc * E * Fin.cases (0 : ℝ) s i.castSucc := by
    cases i.castSucc using Fin.cases <;> simp
  rw [hmul]
  ring

/-- The lower-triangular matrix is the literal Fréchet derivative of
the post-binding catalytic currents in free-substrate coordinates. -/
theorem sourceBindingCurrentAtFree_fderiv {n : ℕ}
    (k : Rates n) (p q : Fin (n+1) → ℝ)
    (S0 E F : ℝ) (s : Fin n → ℝ) :
    fderiv ℝ (sourceBindingCurrentAtFree k p q S0 E F) s =
      (Matrix.mulVecBilin ℝ ℝ
        (sourceBindingCurrentSubstrateJacobian k p q E F)).toContinuousLinearMap := by
  have hfun : sourceBindingCurrentAtFree k p q S0 E F =
      fun v => (sourceBindingCurrentSubstrateJacobian k p q E F).mulVec v +
        sourceBindingCurrentAtFree k p q S0 E F 0 := by
    funext v
    exact sourceBindingCurrentAtFree_affine k p q S0 E F v
  rw [hfun]
  change fderiv ℝ (fun v =>
      (Matrix.mulVecBilin ℝ ℝ
        (sourceBindingCurrentSubstrateJacobian k p q E F)).toContinuousLinearMap v +
        sourceBindingCurrentAtFree k p q S0 E F 0) s = _
  rw [fderiv_add_const]
  exact (Matrix.mulVecBilin ℝ ℝ
    (sourceBindingCurrentSubstrateJacobian k p q E F)).toContinuousLinearMap.hasFDerivAt.fderiv

theorem sourceBindingCurrentSubstrateJacobian_lowerTriangular {n : ℕ}
    (k : Rates n) (p q : Fin (n+1) → ℝ) (E F : ℝ) :
    (sourceBindingCurrentSubstrateJacobian k p q E F).BlockTriangular
      (OrderDual.toDual : Fin n → OrderDual (Fin n)) := by
  intro i j hji
  have hlt : i < j := hji
  have hneq : j.succ ≠ i.castSucc := by
    intro h
    have hv := congrArg Fin.val h
    simp only [Fin.val_succ, Fin.val_castSucc] at hv
    omega
  have hne : j ≠ i := ne_of_gt hlt
  simp [sourceBindingCurrentSubstrateJacobian, hneq, hne]

theorem sourceBindingCurrentSubstrateJacobian_diag {n : ℕ}
    (k : Rates n) (p q : Fin (n+1) → ℝ) (E F : ℝ)
    (i : Fin n) :
    sourceBindingCurrentSubstrateJacobian k p q E F i i =
      -(k.gamma i * q i.succ * F) := by
  have hneq : i.succ ≠ i.castSucc := by
    intro h
    have hv := congrArg Fin.val h
    simp only [Fin.val_succ, Fin.val_castSucc] at hv
    omega
  simp [sourceBindingCurrentSubstrateJacobian, hneq]

-- The two branches use the lemma names in mathlib 4.35 and 4.30.
set_option linter.unusedTactic false in
set_option linter.unreachableTactic false in
theorem sourceBindingCurrentSubstrateJacobian_det {n : ℕ}
    (k : Rates n) (p q : Fin (n+1) → ℝ) (E F : ℝ) :
    (sourceBindingCurrentSubstrateJacobian k p q E F).det =
      (-1 : ℝ)^n * ∏ i : Fin n, k.gamma i * q i.succ * F := by
  first
  | rw [Matrix.det_of_isLowerTriangular _
      (sourceBindingCurrentSubstrateJacobian_lowerTriangular k p q E F)]
  | rw [Matrix.det_of_lowerTriangular _
      (sourceBindingCurrentSubstrateJacobian_lowerTriangular k p q E F)]
  simp_rw [sourceBindingCurrentSubstrateJacobian_diag]
  rw [Finset.prod_neg]
  simp

theorem sourceBindingCurrentSubstrateJacobian_parity_det_pos {n : ℕ}
    (k : Rates n) (p q : Fin (n+1) → ℝ) (E F : ℝ)
    (hk : k.Positive) (hq : ∀ i : Fin n, 0 < q i.succ)
    (hF : 0 < F) :
    0 < (-1 : ℝ)^n *
      (sourceBindingCurrentSubstrateJacobian k p q E F).det := by
  rw [sourceBindingCurrentSubstrateJacobian_det]
  have hsign : (-1 : ℝ)^n * (-1 : ℝ)^n = 1 := by
    rcases neg_one_pow_eq_or ℝ n with h | h <;> simp [h]
  rw [← mul_assoc, hsign, one_mul]
  apply Finset.prod_pos
  intro i _
  exact mul_pos (mul_pos (hk i).2.2.2.2.2 (hq i)) hF

end
end PhosphorylationStableCapacity
