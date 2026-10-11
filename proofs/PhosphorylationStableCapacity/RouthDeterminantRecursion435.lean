module
public import proofs.PhosphorylationStableCapacity.LocalRouthAlternation435
public import Mathlib.LinearAlgebra.Matrix.Block

@[expose] public section

namespace PhosphorylationStableCapacity

open Matrix Polynomial
open scoped BigOperators

/-- Descending coefficients of one Routh reduction. Negative indices
are permitted so the boundary cancellation can be proved explicitly. -/
def routhReducedCoefficients {R : Type*} [Ring R]
    (a : ℤ → R) (c : R) (s : ℤ) : R :=
  if s % 2 = 0 then a (s+1) else a (s+1)-c*a (s+2)

def routhSequenceMatrix {R : Type*} [Ring R]
    (a : ℤ → R) (k : ℕ) : Matrix (Fin k) (Fin k) R :=
  fun i j => a (2*(i.val : ℤ)-(j.val : ℤ)+1)

/-- Simultaneously subtract c times each even-numbered column from
the following odd-numbered column. The matrix is upper triangular
with diagonal one, including at the first eliminated column. -/
def routhEliminationMatrix {R : Type*} [Ring R]
    (k : ℕ) (c : R) : Matrix (Fin k) (Fin k) R :=
  let E : Matrix (Fin k) (Fin k) R :=
    fun i j => if j.val % 2 = 1 ∧ j.val = i.val+1 then -c else 0
  (1 : Matrix (Fin k) (Fin k) R) + E

/-- The finite polynomial represented by the reduced coefficients. -/
noncomputable def routhReducedPolynomial {R : Type*} [Field R]
    (d : ℕ) (p : R[X]) : R[X] :=
  let a := routhDescendingCoeff d p
  let c := a 0 / a 1
  ∑ n ∈ Finset.range d,
    Polynomial.monomial n (routhReducedCoefficients a c ((d : ℤ)-1-(n : ℤ)))

noncomputable section

/-- Applied entries keep the matrix addition typed before exposing its scalars. -/
theorem routhEliminationMatrix_apply {R : Type*} [Ring R]
    (k : ℕ) (c : R) (i j : Fin k) :
    routhEliminationMatrix k c i j =
      (1 : Matrix (Fin k) (Fin k) R) i j +
        (if j.val % 2 = 1 ∧ j.val = i.val+1 then -c else 0) := by
  rfl

theorem routhEliminationMatrix_det {R : Type*} [CommRing R]
    (k : ℕ) (c : R) : (routhEliminationMatrix k c).det = 1 := by
  classical
  have htri : (routhEliminationMatrix k c).IsUpperTriangular := by
    intro i j hij
    rw [routhEliminationMatrix_apply]
    have hne : i ≠ j := by intro h; subst j; simp at hij
    have hnot : ¬ (j.val % 2 = 1 ∧ j.val = i.val+1) := by
      intro h
      have hv : j.val < i.val := hij
      omega
    simp only [Matrix.one_apply, ite_eq_right hne, ite_eq_right hnot, add_zero]
  rw [Matrix.det_of_isUpperTriangular htri]
  apply Finset.prod_eq_one
  intro i _
  have hnot : ¬ (i.val % 2 = 1 ∧ i.val = i.val+1) := by omega
  rw [routhEliminationMatrix_apply]
  simp only [Matrix.one_apply, ite_true, ite_eq_right hnot, add_zero]

theorem routhEliminationMatrix_mul_zero {R : Type*} [CommRing R]
    (k : ℕ) (c : R) (M : Matrix (Fin (k+1)) (Fin (k+1)) R)
    (i : Fin (k+1)) :
    (M*routhEliminationMatrix (k+1) c) i 0 = M i 0 := by
  have hentry (u : Fin (k+1)) :
      routhEliminationMatrix (k+1) c u 0 =
        (1 : Matrix (Fin (k+1)) (Fin (k+1)) R) u 0 := by
    rw [routhEliminationMatrix_apply]
    simp
  rw [Matrix.mul_apply]
  simp_rw [hentry]
  rw [← Matrix.mul_apply, Matrix.mul_one]

theorem routhEliminationMatrix_mul_succ {R : Type*} [CommRing R]
    (k : ℕ) (c : R) (M : Matrix (Fin (k+1)) (Fin (k+1)) R)
    (i : Fin (k+1)) (j : Fin k) :
    (M*routhEliminationMatrix (k+1) c) i j.succ =
      if (j.val+1) % 2 = 1 then M i j.succ-c*M i j.castSucc
        else M i j.succ := by
  classical
  have hidentity :
      (∑ u, M i u * (1 : Matrix (Fin (k+1)) (Fin (k+1)) R) u j.succ) =
        M i j.succ := by
    rw [← Matrix.mul_apply, Matrix.mul_one]
  rw [Matrix.mul_apply]
  simp_rw [routhEliminationMatrix_apply, mul_add]
  rw [Finset.sum_add_distrib, hidentity]
  by_cases hodd : (j.val+1) % 2 = 1
  · have hentry (u : Fin (k+1)) :
        (if j.succ.val % 2 = 1 ∧ j.succ.val = u.val+1 then -c else 0) =
          if u = j.castSucc then -c else 0 := by
      have heq : j.val+1 = u.val+1 ↔ u = j.castSucc := by
        simp only [Fin.ext_iff, Fin.val_castSucc]
        omega
      simp only [Fin.val_succ, hodd, true_and]
      by_cases hu : u = j.castSucc
      · have hnat : j.val+1 = u.val+1 := heq.mpr hu
        simp only [ite_eq_left hnat, ite_eq_left hu]
      · have hnat : ¬ (j.val+1 = u.val+1) := mt heq.mp hu
        simp only [ite_eq_right hnat, ite_eq_right hu]
    simp only [hentry, ite_eq_left hodd, mul_ite, mul_zero,
      Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    ring
  · simp only [Fin.val_succ, hodd, false_and, ite_false, mul_zero,
      Finset.sum_const_zero, add_zero]

/-- The lower-right block after elimination is exactly the next
Hurwitz matrix. This proves the coefficient parity rules rather than
relying on an externally generated Routh array. -/
theorem routhSequenceMatrix_eliminated_block {R : Type*} [CommRing R]
    (a : ℤ → R) (c : R) (k : ℕ) :
    (routhSequenceMatrix a (k+1)*routhEliminationMatrix (k+1) c).submatrix
      Fin.succ Fin.succ = routhSequenceMatrix (routhReducedCoefficients a c) k := by
  ext i j
  rw [Matrix.submatrix_apply, routhEliminationMatrix_mul_succ]
  have harg : 2*((i.val : ℤ)+1)-((j.val : ℤ)+1)+1 =
      (2*(i.val : ℤ)-(j.val : ℤ)+1)+1 := by omega
  have hprev : 2*((i.val : ℤ)+1)-(j.val : ℤ)+1 =
      (2*(i.val : ℤ)-(j.val : ℤ)+1)+2 := by omega
  have hparity : (j.val+1) % 2 = 1 ↔
      ¬ ((2*(i.val : ℤ)-(j.val : ℤ)+1) % 2 = 0) := by omega
  dsimp [routhSequenceMatrix, routhReducedCoefficients]
  rw [harg, hprev]
  by_cases hodd : (j.val+1) % 2 = 1
  · have heven := hparity.mp hodd
    simp only [ite_eq_left hodd, ite_eq_right heven]
  · have heven : (2*(i.val : ℤ)-(j.val : ℤ)+1) % 2 = 0 := by
      omega
    simp only [ite_eq_right hodd, ite_eq_left heven]

/-- The top row is genuinely eliminated: index -1 cancels using
a0=c*a1, and all other out-of-range entries vanish by support. -/
theorem routhSequenceMatrix_eliminated_top {R : Type*} [CommRing R]
    (a : ℤ → R) (c : R) (k : ℕ)
    (hneg : ∀ s : ℤ, s < 0 → a s = 0) (hcancel : a 0 = c*a 1) :
    (routhSequenceMatrix a (k+1)*routhEliminationMatrix (k+1) c) 0 0 = a 1 ∧
    ∀ j : Fin k,
      (routhSequenceMatrix a (k+1)*routhEliminationMatrix (k+1) c) 0 j.succ = 0 := by
  constructor
  · rw [routhEliminationMatrix_mul_zero]
    simp [routhSequenceMatrix]
  · intro j
    rw [routhEliminationMatrix_mul_succ]
    dsimp [routhSequenceMatrix]
    by_cases hj : j.val = 0
    · simp [hj, hcancel]
    · have hlow : a (0-((j.val : ℤ)+1)+1) = 0 :=
        hneg _ (by omega)
      rw [hlow]
      split_ifs with hodd
      · have hjlarge : 2 ≤ j.val := by omega
        rw [hneg _ (by simp; omega)]
        simp
      · rfl

/-- Uniform determinant recursion for an exact Routh reduction. -/
theorem routhSequenceMatrix_det_reduction {R : Type*} [CommRing R]
    (a : ℤ → R) (c : R) (k : ℕ)
    (hneg : ∀ s : ℤ, s < 0 → a s = 0) (hcancel : a 0 = c*a 1) :
    (routhSequenceMatrix a (k+1)).det =
      a 1*(routhSequenceMatrix (routhReducedCoefficients a c) k).det := by
  let H : Matrix (Fin (k+1)) (Fin (k+1)) R :=
    routhSequenceMatrix a (k+1)*routhEliminationMatrix (k+1) c
  have htop : H 0 0 = a 1 ∧ ∀ j : Fin k, H 0 j.succ = 0 :=
    routhSequenceMatrix_eliminated_top a c k hneg hcancel
  obtain ⟨h00, hrow⟩ := htop
  have hdet : H.det = (routhSequenceMatrix a (k+1)).det := by
    simp only [H, Matrix.det_mul, routhEliminationMatrix_det, mul_one]
  rw [← hdet, Matrix.det_succ_row_zero, Fin.sum_univ_succ]
  have hsum : (∑ j : Fin k, (-1 : R)^j.succ.val * H 0 j.succ *
      (H.submatrix Fin.succ j.succ.succAbove).det) = 0 := by
    apply Finset.sum_eq_zero
    intro j _
    rw [hrow]
    simp
  rw [hsum]
  simp only [Fin.val_zero, pow_zero, one_mul, add_zero, h00, Fin.succAbove_zero,
    H, routhSequenceMatrix_eliminated_block]

theorem routhReducedCoefficients_negative {R : Type*} [Ring R]
    (a : ℤ → R) (c : R)
    (hneg : ∀ s : ℤ, s < 0 → a s = 0) (hcancel : a 0 = c*a 1)
    (s : ℤ) (hs : s < 0) : routhReducedCoefficients a c s = 0 := by
  by_cases hsone : s = -1
  · subst s
    simp [routhReducedCoefficients, hcancel]
  · have hs1 : s+1 < 0 := by omega
    unfold routhReducedCoefficients
    rw [hneg _ hs1]
    split_ifs with heven
    · rfl
    · have hs2 : s+2 < 0 := by omega
      rw [hneg _ hs2]
      simp

theorem routhReducedCoefficients_support {R : Type*} [Ring R]
    (a : ℤ → R) (c : R) (d : ℕ)
    (hsupport : ∀ s : ℤ, (d : ℤ) < s → a s = 0)
    (s : ℤ) (hs : (d : ℤ)-1 < s) : routhReducedCoefficients a c s = 0 := by
  unfold routhReducedCoefficients
  rw [hsupport _ (by omega)]
  split_ifs
  · rfl
  · rw [hsupport _ (by omega)]
    simp

theorem routhReducedPolynomial_coeff {R : Type*} [Field R]
    (d : ℕ) (p : R[X]) (n : ℕ) :
    (routhReducedPolynomial d p).coeff n =
      if n < d then routhReducedCoefficients (routhDescendingCoeff d p)
        (routhDescendingCoeff d p 0 / routhDescendingCoeff d p 1)
        ((d : ℤ)-1-(n : ℤ)) else 0 := by
  classical
  simp [routhReducedPolynomial, Polynomial.coeff_monomial]

/-- The finite polynomial producer and descending-sequence reduction
agree even at negative indices; the a0/a1 boundary is not discarded. -/
theorem routhReducedPolynomial_descending {R : Type*} [Field R]
    (d : ℕ) (hd : 0 < d) (p : R[X])
    (hpivot : routhDescendingCoeff d p 1 ≠ 0) (s : ℤ) :
    routhDescendingCoeff (d-1) (routhReducedPolynomial d p) s =
      routhReducedCoefficients (routhDescendingCoeff d p)
        (routhDescendingCoeff d p 0 / routhDescendingCoeff d p 1) s := by
  let a := routhDescendingCoeff d p
  let c := a 0 / a 1
  have hneg : ∀ t : ℤ, t < 0 → a t = 0 := by
    intro t ht
    simp [a, routhDescendingCoeff, show ¬ (0 ≤ t ∧ t ≤ (d : ℤ)) by omega]
  have hsupport : ∀ t : ℤ, (d : ℤ) < t → a t = 0 := by
    intro t ht
    simp [a, routhDescendingCoeff, show ¬ (0 ≤ t ∧ t ≤ (d : ℤ)) by omega]
  have hcancel : a 0 = c*a 1 := by
    exact (div_mul_cancel₀ (a 0) hpivot).symm
  change (if 0 ≤ s ∧ s ≤ ((d-1 : ℕ) : ℤ) then
      (routhReducedPolynomial d p).coeff (d-1-s.toNat) else 0) =
    routhReducedCoefficients a c s
  by_cases hs : 0 ≤ s ∧ s ≤ ((d-1 : ℕ) : ℤ)
  · have hn : d-1-s.toNat < d := by omega
    rw [ite_eq_left hs, routhReducedPolynomial_coeff, ite_eq_left hn]
    congr 1
    omega
  · rw [ite_eq_right hs]
    by_cases hnegative : s < 0
    · exact (routhReducedCoefficients_negative a c hneg hcancel s hnegative).symm
    · have hlarge : (d : ℤ)-1 < s := by omega
      exact (routhReducedCoefficients_support a c d hsupport s hlarge).symm

/-- Exact polynomial Hurwitz-minor recursion, at every finite order.
The spectral preservation of this reduction is a distinct theorem;
no Hurwitz assumption is silently replaced by positive pivots here. -/
theorem routhHurwitzMinor_reduction {R : Type*} [Field R]
    (d : ℕ) (hd : 0 < d) (p : R[X])
    (hpivot : routhDescendingCoeff d p 1 ≠ 0) (k : ℕ) :
    routhHurwitzMinor d (k+1) p =
      routhDescendingCoeff d p 1 *
        routhHurwitzMinor (d-1) k (routhReducedPolynomial d p) := by
  let a := routhDescendingCoeff d p
  let c := a 0 / a 1
  have hneg : ∀ s : ℤ, s < 0 → a s = 0 := by
    intro s hs
    simp [a, routhDescendingCoeff, show ¬ (0 ≤ s ∧ s ≤ (d : ℤ)) by omega]
  have hcancel : a 0 = c*a 1 := (div_mul_cancel₀ (a 0) hpivot).symm
  have hsequence : routhSequenceMatrix (routhReducedCoefficients a c) k =
      routhHurwitzMatrix (d-1) k (routhReducedPolynomial d p) := by
    ext i j
    exact (routhReducedPolynomial_descending d hd p hpivot _).symm
  unfold routhHurwitzMinor
  change (routhSequenceMatrix a (k+1)).det = _
  rw [routhSequenceMatrix_det_reduction a c k hneg hcancel, hsequence]

/-- Polynomial normalization scales the k-th minor by the k-th power
of its scalar. This supplies the exact monic-normalization step for
an eventual induction on a positive leading Routh pivot. -/
theorem routhHurwitzMinor_C_mul {R : Type*} [CommRing R]
    (d k : ℕ) (p : R[X]) (c : R) :
    routhHurwitzMinor d k (Polynomial.C c*p) =
      c^k*routhHurwitzMinor d k p := by
  have hH : routhHurwitzMatrix d k (Polynomial.C c*p) =
      c • routhHurwitzMatrix d k p := by
    ext i j
    dsimp [routhHurwitzMatrix, routhDescendingCoeff]
    split_ifs <;> simp [Polynomial.coeff_C_mul]
  unfold routhHurwitzMinor
  rw [hH, Matrix.det_smul]
  simp

/-- A positive first pivot transfers minor positivity exactly to the
explicit reduced polynomial. This is algebraic transfer, not an
assumed spectral preservation theorem. -/
theorem routhHurwitzMinor_pos_iff_reduced
    (d : ℕ) (hd : 0 < d) (p : ℝ[X])
    (hpivot : 0 < routhDescendingCoeff d p 1) (k : ℕ) :
    0 < routhHurwitzMinor d (k+1) p ↔
      0 < routhHurwitzMinor (d-1) k (routhReducedPolynomial d p) := by
  rw [routhHurwitzMinor_reduction d hd p (ne_of_gt hpivot) k]
  exact mul_pos_iff_of_pos_left hpivot

end
end PhosphorylationStableCapacity
