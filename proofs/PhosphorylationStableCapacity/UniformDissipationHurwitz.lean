module
public import proofs.PhosphorylationStableCapacity.PositiveDefiniteLyapunovHurwitz
public import proofs.PhosphorylationStableCapacity.QuantitativeMatrixDissipation
public import Mathlib.LinearAlgebra.Matrix.PosDef

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section
open Matrix
open scoped BigOperators

/-- A strict uniform quadratic dissipation bound proves the full Hurwitz
condition for the actual real Jacobian, including nonsymmetric matrices. -/
theorem hurwitz_of_uniform_quadratic_dissipation
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A P : Matrix ι ι ℝ) (hP : P.PosDef) (c : ℝ) (hc : 0 < c)
    (hdiss : ∀ v : ι → ℝ,
      2 * (v ⬝ᵥ (P *ᵥ (A *ᵥ v))) ≤ -c * (∑ i, v i ^ 2)) :
    ∀ z : ℂ, ((A.map (algebraMap ℝ ℂ)).charpoly).eval z = 0 → z.re < 0 := by
  let Q : Matrix ι ι ℝ := -(A.transpose * P + P * A)
  have hPtranspose : P.transpose = P := by
    have h := hP.isHermitian
    change Pᴴ = P at h
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using h
  have hQherm : Q.IsHermitian := by
    change Qᴴ = Q
    rw [Matrix.conjTranspose_eq_transpose_of_trivial]
    simp only [Q, Matrix.transpose_neg, Matrix.transpose_add,
      Matrix.transpose_mul, Matrix.transpose_transpose,
      hPtranspose]
    ac_rfl
  have hQ : Q.PosDef := by
    apply Matrix.PosDef.of_dotProduct_mulVec_pos hQherm
    intro v hv
    have hnonzero : ∃ i, v i ≠ 0 := by
      by_contra h
      push Not at h
      apply hv
      funext i
      exact h i
    obtain ⟨i, hi⟩ := hnonzero
    have hnorm : 0 < ∑ j, v j ^ 2 :=
      (sq_pos_of_ne_zero hi).trans_le
        (Finset.single_le_sum (fun j _ => sq_nonneg (v j)) (Finset.mem_univ i))
    have hidentity := symmetric_matrix_lyapunov_directional_identity
      A P hP.isHermitian.isSymm v
    have hd := hdiss v
    change 0 < star v ⬝ᵥ (Q *ᵥ v)
    simp only [star_trivial, Q, Matrix.neg_mulVec, dotProduct_neg]
    nlinarith [mul_pos hc hnorm]
  apply hurwitz_of_posDef_lyapunov A P Q hP hQ
  simp only [Q, neg_neg]

end
end PhosphorylationStableCapacity
