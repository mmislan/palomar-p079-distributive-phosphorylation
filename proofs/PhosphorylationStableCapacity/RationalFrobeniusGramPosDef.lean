module
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.Data.Rat.Star
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Tactic.Linarith

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section

open Matrix

/-- The rational squared Frobenius norm controls the squared length of
every rational vector.  This keeps the Lyapunov certificate entirely in
exact arithmetic. -/
theorem rational_frobenius_mulVec_sq_bound {ι : Type*}
    [Fintype ι] [DecidableEq ι]
    (B : Matrix ι ι ℚ) (x : ι → ℚ) :
    (∑ i, (B *ᵥ x) i ^ 2) ≤
      (∑ i, ∑ j, (B i j)^2) * (∑ j, (x j)^2) := by
  have hrow (i : ι) :
      (B *ᵥ x) i ^ 2 ≤
        (∑ j, (B i j)^2) * (∑ j, (x j)^2) := by
    simpa [Matrix.mulVec, dotProduct] using
      (Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset ι)
        (fun j => B i j) x)
  calc
    (∑ i, (B *ᵥ x) i ^ 2) ≤
        ∑ i, (∑ j, (B i j)^2) * (∑ j, (x j)^2) :=
      Finset.sum_le_sum (fun i _ => hrow i)
    _ = (∑ i, ∑ j, (B i j)^2) * (∑ j, (x j)^2) := by
      rw [Finset.sum_mul]

/-- A strict rational Frobenius contraction makes `I-BᵀB` positive
definite over the rationals, not just after embedding into the reals. -/
theorem rational_one_sub_gram_posDef {ι : Type*}
    [Fintype ι] [DecidableEq ι]
    (B : Matrix ι ι ℚ)
    (hB : (∑ i, ∑ j, (B i j)^2) < 1) :
    (1 - B.transpose * B).PosDef := by
  have hgram : (B.transpose * B).IsHermitian := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
      (Matrix.isHermitian_conjTranspose_mul_self B)
  refine Matrix.PosDef.of_dotProduct_mulVec_pos
    (Matrix.isHermitian_one.sub hgram) ?_
  intro x hx
  have hS : 0 < ∑ i, (x i)^2 := by
    have hxx : 0 < x ⬝ᵥ x := by
      simpa only [star_trivial] using
        (Matrix.dotProduct_star_self_pos_iff.mpr hx)
    simpa only [dotProduct, pow_two] using hxx
  have hbound := rational_frobenius_mulVec_sq_bound B x
  have hmargin :
      (∑ i, ∑ j, (B i j)^2) * (∑ i, (x i)^2) <
        ∑ i, (x i)^2 := by
    have hm := mul_pos (sub_pos.mpr hB) hS
    nlinarith
  have hquad :
      x ⬝ᵥ ((1 - B.transpose * B) *ᵥ x) =
        (∑ i, (x i)^2) - (∑ i, (B *ᵥ x) i ^ 2) := by
    calc
      x ⬝ᵥ ((1 - B.transpose * B) *ᵥ x) =
          x ⬝ᵥ x - x ⬝ᵥ ((B.transpose * B) *ᵥ x) := by
        rw [Matrix.sub_mulVec, dotProduct_sub, Matrix.one_mulVec]
      _ = x ⬝ᵥ x - (B *ᵥ x) ⬝ᵥ (B *ᵥ x) := by
        rw [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec,
          Matrix.vecMul_transpose]
      _ = (∑ i, (x i)^2) - (∑ i, (B *ᵥ x) i ^ 2) := by
        simp only [dotProduct, pow_two]
  simpa only [star_trivial, hquad, sub_pos] using
    (lt_of_le_of_lt hbound hmargin)

end
end PhosphorylationStableCapacity
