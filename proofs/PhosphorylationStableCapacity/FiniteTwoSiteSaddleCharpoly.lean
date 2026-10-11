module
public import proofs.PhosphorylationStableCapacity.FiniteTwoSiteRationalCertificate
public import proofs.PhosphorylationStableCapacity.TwoSiteSaddlePolynomialData
public import proofs.PhosphorylationStableCapacity.FiniteTwoSiteSaddleCharpolyPilot
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Tactic.ComputeDegree

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

/-- Closed exact characteristic-polynomial certificate for the printed middle
two-site equilibrium's proposed rational Jacobian matrix. -/
theorem manuscriptTwoSiteA1_charpoly :
    manuscriptTwoSiteA1.charpoly = twoSiteSaddlePolyQ := by
  apply Polynomial.eq_of_natDegree_lt_card_of_eval_eq
    (f := fun i : Fin 7 => (i.val : ℚ))
  · intro i j h
    have hval : (i.val : ℚ) = (j.val : ℚ) := h
    exact Fin.ext (by exact_mod_cast hval)
  · intro i
    fin_cases i
    · exact manuscriptTwoSiteA1_charpoly_eval_zero
    · exact manuscriptTwoSiteA1_charpoly_eval_one
    · exact manuscriptTwoSiteA1_charpoly_eval_two
    · exact manuscriptTwoSiteA1_charpoly_eval_three
    · exact manuscriptTwoSiteA1_charpoly_eval_four
    · exact manuscriptTwoSiteA1_charpoly_eval_five
    · exact manuscriptTwoSiteA1_charpoly_eval_six
  · have hp : twoSiteSaddlePolyQ.natDegree ≤ 6 := by
      unfold twoSiteSaddlePolyQ
      compute_degree!
    simp only [Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]
    omega

end
end PhosphorylationStableCapacity
