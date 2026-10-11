module
public import Mathlib.Data.Rat.Star
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.LinearAlgebra.Matrix.SchurComplement
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.Logic.Equiv.Fin.Basic
public import Mathlib.Tactic.FinCases

public import proofs.PhosphorylationStableCapacity.RationalPosDefCongruence
public import proofs.PhosphorylationStableCapacity.FiniteRouthLDLSearchDefinition

@[expose] public section
set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

namespace PhosphorylationStableCapacity

open Matrix

/-- Reindex a rational matrix so its last row and column form a one by one block. -/
def rationalLastBlock {n : ℕ} (M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℚ) :
    Matrix (Fin n ⊕ Fin 1) (Fin n ⊕ Fin 1) ℚ :=
  M.submatrix finSumFinEquiv finSumFinEquiv

/-- The exact rational Schur complement of the last entry.  This formula uses
ordinary rational inversion, rather than the noncomputable matrix inverse. -/
def rationalSchurStep {n : ℕ} (M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℚ) :
    Matrix (Fin n) (Fin n) ℚ :=
  let X := rationalLastBlock M
  let A := X.toBlocks₁₁
  let B := X.toBlocks₁₂
  let D := X.toBlocks₂₂
  A - B * Matrix.diagonal (fun _ : Fin 1 => (D 0 0)⁻¹) * B.transpose

/-- A total finite rational-arithmetic test.  Each recursive step checks
symmetry and a positive pivot, then eliminates that pivot.  It returns `false`
on singular or indefinite matrices; no certificate enumeration is involved. -/
def rationalPosDefDecide : (n : ℕ) → Matrix (Fin n) (Fin n) ℚ → Bool
  | 0, _ => true
  | n + 1, M =>
      decide M.IsSymm &&
        decide (0 < (rationalLastBlock M).toBlocks₂₂ 0 0) &&
          rationalPosDefDecide n (rationalSchurStep M)

/-- The explicit scalar rational inverse used by the test is the nonsingular
inverse of its one by one block. -/
private theorem fin_one_inverse_eq_diagonal (D : Matrix (Fin 1) (Fin 1) ℚ) :
    D⁻¹ = Matrix.diagonal (fun _ : Fin 1 => (D 0 0)⁻¹) := by
  rw [Matrix.inv_subsingleton]
  ext i j
  fin_cases i
  fin_cases j
  simp [Ring.inverse_eq_inv]

/-- The exact pivot test agrees with positive definiteness of the final
one by one block. -/
private theorem fin_one_posDef_iff (D : Matrix (Fin 1) (Fin 1) ℚ) :
    D.PosDef ↔ 0 < D 0 0 := by
  have hdiag : D = Matrix.diagonal (fun _ : Fin 1 => D 0 0) := by
    ext i j
    fin_cases i
    fin_cases j
    simp
  rw [hdiag, Matrix.posDef_diagonal_iff]
  simp

/-- A Schur reduction with a positive bottom-right block preserves and
reflects strict positive definiteness.  The semidefinite block theorem and
the determinant identity together supply the strict implication. -/
private theorem posDef_fromBlocks_iff_schur {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℚ)
    (B : Matrix (Fin n) (Fin 1) ℚ)
    (D : Matrix (Fin 1) (Fin 1) ℚ) (hD : D.PosDef) :
    (Matrix.fromBlocks A B B.transpose D).PosDef ↔
      (A - B * D⁻¹ * B.transpose).PosDef := by
  let : Invertible D := hD.isUnit.invertible
  let S : Matrix (Fin n) (Fin n) ℚ := A - B * D⁻¹ * B.transpose
  have hsemidef :
      (Matrix.fromBlocks A B B.transpose D).PosSemidef ↔ S.PosSemidef := by
    simpa only [S, Matrix.conjTranspose_eq_transpose_of_trivial] using
      Matrix.PosDef.fromBlocks₂₂ A B hD
  have hdet :
      (Matrix.fromBlocks A B B.transpose D).det ≠ 0 ↔ S.det ≠ 0 := by
    rw [Matrix.det_fromBlocks₂₂, Matrix.invOf_eq_nonsing_inv]
    exact mul_ne_zero_iff_left (ne_of_gt hD.det_pos)
  constructor
  · intro h
    have hs : S.PosSemidef := hsemidef.mp h.posSemidef
    exact hs.posDef_iff_det_ne_zero.mpr (hdet.mp (ne_of_gt h.det_pos))
  · intro h
    have hf : (Matrix.fromBlocks A B B.transpose D).PosSemidef :=
      hsemidef.mpr h.posSemidef
    exact hf.posDef_iff_det_ne_zero.mpr (hdet.mpr (ne_of_gt h.det_pos))

/-- The rational Schur test is sound and complete for positive definiteness.
This theorem concerns one fixed rational symmetric matrix and does not make
the manuscript's outer ordered parameter search terminate. -/
theorem rationalPosDefDecide_iff :
    ∀ (n : ℕ) (M : Matrix (Fin n) (Fin n) ℚ),
      rationalPosDefDecide n M = true ↔ M.PosDef := by
  intro n
  induction n with
  | zero =>
      intro M
      constructor
      · intro _
        have hM : M = 1 := by
          ext i j
          exact Fin.elim0 i
        rw [hM]
        exact Matrix.PosDef.one
      · intro _
        rfl
  | succ n ih =>
      intro M
      let e : Fin n ⊕ Fin 1 ≃ Fin (n + 1) := finSumFinEquiv
      let X : Matrix (Fin n ⊕ Fin 1) (Fin n ⊕ Fin 1) ℚ :=
        M.submatrix e e
      let A : Matrix (Fin n) (Fin n) ℚ := X.toBlocks₁₁
      let B : Matrix (Fin n) (Fin 1) ℚ := X.toBlocks₁₂
      let D : Matrix (Fin 1) (Fin 1) ℚ := X.toBlocks₂₂
      have hreindex : X.PosDef ↔ M.PosDef := by
        constructor
        · intro h
          have h' := h.submatrix e.symm.injective
          simpa [X, Matrix.submatrix_submatrix] using h'
        · intro h
          exact h.submatrix e.injective
      have hschur : rationalSchurStep M =
          A - B * D⁻¹ * B.transpose := by
        simp only [rationalSchurStep, rationalLastBlock, X, A, B, D]
        rw [fin_one_inverse_eq_diagonal]
      constructor
      · intro h
        have hbool : decide M.IsSymm = true ∧
            decide (0 < (rationalLastBlock M).toBlocks₂₂ 0 0) = true ∧
            rationalPosDefDecide n (rationalSchurStep M) = true := by
          simpa only [rationalPosDefDecide, Bool.and_eq_true, and_assoc] using h
        have hM : M.IsSymm := of_decide_eq_true hbool.1
        have hpivot : 0 < D 0 0 := of_decide_eq_true hbool.2.1
        have hrec : rationalPosDefDecide n (rationalSchurStep M) = true :=
          hbool.2.2
        have hX : X.IsSymm := by
          apply Matrix.IsSymm.ext
          intro i j
          exact hM.apply (e i) (e j)
        have hC : X.toBlocks₂₁ = B.transpose := by
          ext i j
          simpa only [B, Matrix.toBlocks₂₁, Matrix.toBlocks₁₂,
            Matrix.transpose_apply, Matrix.of_apply] using
            hX.apply (Sum.inl j) (Sum.inr i)
        have hblocks : X = Matrix.fromBlocks A B B.transpose D := by
          rw [← Matrix.fromBlocks_toBlocks X, hC]
        have hD : D.PosDef := (fin_one_posDef_iff D).mpr hpivot
        have hS : (A - B * D⁻¹ * B.transpose).PosDef := by
          rw [← hschur]
          exact (ih _).mp hrec
        exact hreindex.mp (hblocks.symm ▸
          (posDef_fromBlocks_iff_schur A B D hD).mpr hS)
      · intro hM
        have hX : X.PosDef := hreindex.mpr hM
        have hC : X.toBlocks₂₁ = B.transpose := by
          ext i j
          simpa only [B, Matrix.toBlocks₂₁, Matrix.toBlocks₁₂,
            Matrix.transpose_apply, Matrix.of_apply] using
            hX.1.isSymm.apply (Sum.inl j) (Sum.inr i)
        have hblocks : X = Matrix.fromBlocks A B B.transpose D := by
          rw [← Matrix.fromBlocks_toBlocks X, hC]
        have hD : D.PosDef := by
          have hD' : X.toBlocks₂₂.PosDef :=
            hX.submatrix Sum.inr_injective
          exact hD'
        have hS : (A - B * D⁻¹ * B.transpose).PosDef :=
          (posDef_fromBlocks_iff_schur A B D hD).mp (hblocks ▸ hX)
        have hrec : rationalPosDefDecide n (rationalSchurStep M) = true :=
          (ih _).mpr (by rw [hschur]; exact hS)
        have hpivot : 0 < D 0 0 := (fin_one_posDef_iff D).mp hD
        have hpivot' : 0 < (rationalLastBlock M).toBlocks₂₂ 0 0 := hpivot
        have hbool : decide M.IsSymm = true ∧
            decide (0 < (rationalLastBlock M).toBlocks₂₂ 0 0) = true ∧
            rationalPosDefDecide n (rationalSchurStep M) = true :=
          ⟨decide_eq_true_eq.mpr hM.1.isSymm,
            decide_eq_true_eq.mpr hpivot', hrec⟩
        simpa only [rationalPosDefDecide, Bool.and_eq_true, and_assoc] using hbool

/-- Convenient soundness form for use by a fixed rational Lyapunov test. -/
theorem rationalPosDefDecide_sound {n : ℕ}
    {M : Matrix (Fin n) (Fin n) ℚ}
    (h : rationalPosDefDecide n M = true) : M.PosDef :=
  (rationalPosDefDecide_iff n M).mp h

/-- Convenient completeness form for use by a fixed rational Lyapunov test. -/
theorem rationalPosDefDecide_complete {n : ℕ}
    {M : Matrix (Fin n) (Fin n) ℚ} (h : M.PosDef) :
    rationalPosDefDecide n M = true :=
  (rationalPosDefDecide_iff n M).mpr h

/-- Positive definiteness is unchanged when a rational matrix is read over
the reals.  The reverse implication restricts the real quadratic inequality
to rational vectors; the forward implication uses exact rational diagonal
congruence factors. -/
theorem rationalMatrix_posDef_cast_iff {n : ℕ}
    (M : Matrix (Fin n) (Fin n) ℚ) :
    (M.map (algebraMap ℚ ℝ)).PosDef ↔ M.PosDef := by
  let f := algebraMap ℚ ℝ
  constructor
  · intro hreal
    have hsym : M.IsSymm := by
      apply Matrix.IsSymm.ext
      intro i j
      have h := hreal.1.isSymm.apply i j
      change (M j i : ℝ) = (M i j : ℝ) at h
      exact_mod_cast h
    apply Matrix.PosDef.of_dotProduct_mulVec_pos
      (Matrix.isHermitian_iff_isSymm.mpr hsym)
    intro x hx
    let xr : Fin n → ℝ := fun i => (x i : ℝ)
    have hxr : xr ≠ 0 := by
      intro hzero
      apply hx
      funext i
      have hi : (x i : ℝ) = 0 := by
        simpa [xr] using congrFun hzero i
      exact_mod_cast hi
    have hform :
        (f (star x ⬝ᵥ (M *ᵥ x))) =
          star xr ⬝ᵥ ((M.map f) *ᵥ xr) := by
      simp only [star_trivial]
      calc
        f (x ⬝ᵥ (M *ᵥ x)) =
            (f ∘ x) ⬝ᵥ (f ∘ (M *ᵥ x)) :=
          RingHom.map_dotProduct f x (M *ᵥ x)
        _ = xr ⬝ᵥ ((M.map f) *ᵥ xr) := by
          congr 1
          funext i
          exact RingHom.map_mulVec f M x i
    have hpositive := hreal.dotProduct_mulVec_pos hxr
    rw [← hform] at hpositive
    change 0 < ((star x ⬝ᵥ (M *ᵥ x) : ℚ) : ℝ) at hpositive
    exact_mod_cast hpositive
  · intro hrat
    obtain ⟨L, R, d, hd, hLR, hfactor⟩ :=
      rational_posDef_has_congruence_factor M hrat
    let DR : Matrix (Fin n) (Fin n) ℝ :=
      Matrix.diagonal (fun i => (d i : ℝ))
    have hDR : DR.PosDef := by
      apply Matrix.PosDef.diagonal
      intro i
      exact_mod_cast hd i
    have hLRreal : (L.map f) * (R.map f) = 1 := by
      calc
        (L.map f) * (R.map f) = (L * R).map f := by
          rw [Matrix.map_mul]
        _ = 1 := by rw [hLR]; simp
    have hMreal :
        M.map f = (L.map f) * DR * (L.map f).transpose := by
      have h := congrArg (fun N : Matrix (Fin n) (Fin n) ℚ => N.map f) hfactor
      simpa [DR, Matrix.map_mul, Matrix.transpose_map,
        Matrix.diagonal_map (map_zero f)] using h
    exact posDef_of_ldl_with_right_inverse
      (M.map f) (L.map f) DR (R.map f) hDR hLRreal hMreal

/-- A finite exact acceptance test for a *specified* rational Lyapunov
identity and its two rational positive-definite matrices.  This makes one
parameter trial halt either way; choosing a successful outer parameter is
a separate theorem. -/
def rationalFixedLyapunovAccepts {n : ℕ}
    (A P Q : Matrix (Fin n) (Fin n) ℚ) : Bool :=
  rationalPosDefDecide n P && rationalPosDefDecide n Q &&
    decide (A.transpose * P + P * A = -Q)

theorem rationalFixedLyapunovAccepts_iff {n : ℕ}
    (A P Q : Matrix (Fin n) (Fin n) ℚ) :
    rationalFixedLyapunovAccepts A P Q = true ↔
      P.PosDef ∧ Q.PosDef ∧ A.transpose * P + P * A = -Q := by
  simp only [rationalFixedLyapunovAccepts, Bool.and_eq_true,
    decide_eq_true_eq, rationalPosDefDecide_iff, and_assoc]

/-- A true result from the total fixed-data rational checker certifies the
actual real Hurwitz spectrum.  This uses rational diagonal-congruence factors
for `P` and `Q`, then the previously defined exact Lyapunov certificate
bridge.  It still says nothing about which outer parameter trial succeeds. -/
theorem rationalFixedLyapunovAccepts_hurwitz {n : ℕ}
    (A P Q : Matrix (Fin n) (Fin n) ℚ)
    (h : rationalFixedLyapunovAccepts A P Q = true) :
    IsHurwitz (A.map (algebraMap ℚ ℝ)) := by
  rcases (rationalFixedLyapunovAccepts_iff A P Q).mp h with
    ⟨hP, hQ, hlyap⟩
  obtain ⟨LP, RP, dP, hdP, hiP, hfP⟩ :=
    rational_posDef_has_congruence_factor P hP
  obtain ⟨LQ, RQ, dQ, hdQ, hiQ, hfQ⟩ :=
    rational_posDef_has_congruence_factor Q hQ
  let C : RationalLyapunovLDLCertificate A := {
    P := P, Q := Q,
    LP := LP, RP := RP, LQ := LQ, RQ := RQ,
    dP := dP, dQ := dQ,
    positiveP := hdP, positiveQ := hdQ,
    inverseP := hiP, inverseQ := hiQ,
    factorP := hfP, factorQ := hfQ,
    lyapunov := hlyap }
  exact C.isHurwitz

end PhosphorylationStableCapacity
