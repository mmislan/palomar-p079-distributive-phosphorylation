module
public import Mathlib.Analysis.Polynomial.Order
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
public import Mathlib.Tactic.Linarith

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section
open Polynomial Matrix

/-- A monic real polynomial negative at zero has a positive real zero. -/
theorem exists_pos_root_of_monic_eval_zero_neg
    (P : ℝ[X]) (hP : P.Monic) (hzero : P.eval 0 < 0) :
    ∃ x : ℝ, 0 < x ∧ P.eval x = 0 := by
  by_contra hnone
  have hroots : ∀ y : ℝ, P.IsRoot y → y < 0 := by
    intro y hy
    by_contra hnot
    have hyge : 0 ≤ y := le_of_not_gt hnot
    rcases eq_or_lt_of_le hyge with hy0 | hypos
    · subst y
      rw [Polynomial.IsRoot.def] at hy
      linarith
    · exact hnone ⟨y, hypos, by simpa only [Polynomial.IsRoot.def] using hy⟩
  have hpositive := P.zero_lt_eval_of_roots_lt_of_leadingCoeff_nonneg
    hroots (by rw [hP.leadingCoeff]; norm_num)
  linarith

/-- For a `3n` class matrix, a negative parity-adjusted determinant forces
a positive real characteristic root. This supplies existence independently
of a numerically tiny eigenvalue and without expanding a determinant. -/
theorem exists_pos_charpoly_root_of_parity_det_neg
    {ι : Type*} [Fintype ι] [DecidableEq ι] (n : ℕ)
    (hcard : Fintype.card ι = 3 * n) (M : Matrix ι ι ℝ)
    (hdet : (-1 : ℝ) ^ n * M.det < 0) :
    ∃ x : ℝ, 0 < x ∧ M.charpoly.eval x = 0 := by
  have hcoeff : M.charpoly.coeff 0 < 0 := by
    have hd := Matrix.det_eq_sign_charpoly_coeff M
    rw [hcard] at hd
    have hs : (-1 : ℝ) ^ (3 * n) = (-1 : ℝ) ^ n := by
      rw [pow_mul]
      norm_num
    rw [hs] at hd
    rcases neg_one_pow_eq_or ℝ n with hpos | hneg
    · rw [hpos] at hdet hd
      simp only [one_mul] at hd hdet
      linarith
    · rw [hneg] at hdet hd
      simp only [neg_one_mul] at hd hdet
      linarith
  apply exists_pos_root_of_monic_eval_zero_neg M.charpoly (Matrix.charpoly_monic M)
  rwa [← Polynomial.coeff_zero_eq_eval_zero]

end
end PhosphorylationStableCapacity
