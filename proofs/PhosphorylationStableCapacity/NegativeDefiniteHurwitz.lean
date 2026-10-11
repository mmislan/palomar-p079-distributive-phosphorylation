module
public import proofs.PhosphorylationStableCapacity.Jacobian
public import Mathlib.Analysis.Matrix.PosDef

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section
open Matrix
open WithLp

/-- A real positive-definite matrix has a Hurwitz negative. -/
theorem isHurwitz_neg_of_posDef {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (hA : A.PosDef) : IsHurwitz (-A) := by
  let hN : (-A).IsHermitian := hA.isHermitian.neg
  have hEig : ∀ i, hN.eigenvalues i < 0 := by
    intro i
    have hv : (⇑(hN.eigenvectorBasis i) : ι → ℝ) ≠ 0 :=
      (ofLp_eq_zero 2).ne.2 (hN.eigenvectorBasis.orthonormal.ne_zero i)
    have hp := hA.dotProduct_mulVec_pos hv
    have he := hN.eigenvalues_eq i
    simp only [RCLike.re_to_real, Matrix.neg_mulVec, dotProduct_neg] at he
    simp only [star_trivial] at he hp
    linarith
  intro z hz
  have hpoly : ((-A).map (algebraMap ℝ ℂ)).charpoly =
      ∏ i, (Polynomial.X - Polynomial.C ((hN.eigenvalues i : ℝ) : ℂ)) := by
    rw [Matrix.charpoly_map, hN.charpoly_eq]
    simp [Polynomial.map_prod, RCLike.algebraMap_eq_ofReal]
  rw [hpoly, Polynomial.eval_prod] at hz
  simp only [Polynomial.eval_sub, Polynomial.eval_X,
    Polynomial.eval_C] at hz
  obtain ⟨i, _, hi⟩ := Finset.prod_eq_zero_iff.mp hz
  have hzi : z = ((hN.eigenvalues i : ℝ) : ℂ) := sub_eq_zero.mp hi
  simpa [hzi] using hEig i

end
end PhosphorylationStableCapacity
