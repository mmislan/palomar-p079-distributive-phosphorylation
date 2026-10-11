module
public import Mathlib.Algebra.Order.Star.Real
public import proofs.PhosphorylationStableCapacity.SymmetricMetzlerEnergy435

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section

/-- The manuscript's explicit diagonal ratio `Pᵢᵢ=wᵢ/zᵢ` is a strict
Lyapunov matrix whenever a Metzler block has positive right and left
strict certificates. -/
theorem explicit_diagonal_lyapunov_of_two_metzler_certificates
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (B : Matrix ι ι ℝ)
    (z w : ι → ℝ)
    (hz : ∀ i, 0 < z i) (hw : ∀ i, 0 < w i)
    (hoff : ∀ i j, i ≠ j → 0 ≤ B i j)
    (hright : ∀ i, (∑ j, B i j * z j) < 0)
    (hleft : ∀ i, (∑ j, B j i * w j) < 0) :
    let P := Matrix.diagonal (fun i => w i / z i)
    P.PosDef ∧ (-(B.transpose * P + P * B)).PosDef ∧
      ∀ i, (∑ j, (B.transpose * P + P * B) i j * z j) < 0 := by
  intro P
  let p : ι → ℝ := fun i => w i / z i
  have hp : ∀ i, 0 < p i := fun i => div_pos (hw i) (hz i)
  have hP : P = Matrix.diagonal p := rfl
  have hPz : ∀ i, p i * z i = w i := by
    intro i
    exact div_mul_cancel₀ (w i) (ne_of_gt (hz i))
  have hQsym : ∀ i j,
      (B.transpose * P + P * B) i j =
        (B.transpose * P + P * B) j i := by
    intro i j
    simp only [Matrix.add_apply, hP, Matrix.mul_diagonal,
      Matrix.diagonal_mul, Matrix.transpose_apply]
    ring
  have hQoff : ∀ i j, i ≠ j →
      0 ≤ (B.transpose * P + P * B) i j := by
    intro i j hij
    simp only [Matrix.add_apply, hP, Matrix.mul_diagonal,
      Matrix.diagonal_mul, Matrix.transpose_apply]
    exact add_nonneg
      (mul_nonneg (hoff j i (Ne.symm hij)) (hp j).le)
      (mul_nonneg (hp i).le (hoff i j hij))
  have hQz : ∀ i,
      (∑ j, (B.transpose * P + P * B) i j * z j) < 0 := by
    intro i
    have hfirst : (∑ j, (B.transpose * P) i j * z j) =
        ∑ j, B j i * w j := by
      simp only [hP, Matrix.mul_diagonal, Matrix.transpose_apply]
      apply Finset.sum_congr rfl
      intro j _
      rw [mul_assoc, hPz]
    have hsecond : (∑ j, (P * B) i j * z j) =
        p i * (∑ j, B i j * z j) := by
      simp only [hP, Matrix.diagonal_mul]
      simp_rw [mul_assoc]
      rw [Finset.mul_sum]
    simp only [Matrix.add_apply, add_mul, Finset.sum_add_distrib]
    rw [hfirst, hsecond]
    exact add_neg (hleft i)
      (mul_neg_of_pos_of_neg (hp i) (hright i))
  refine ⟨?_, symmetric_metzler_neg_posDef _ hQsym hQoff z hz hQz,
    hQz⟩
  rw [hP]
  exact Matrix.posDef_diagonal_iff.mpr hp

end

end PhosphorylationStableCapacity
