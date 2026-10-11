module
public import proofs.PhosphorylationStableCapacity.FiniteTwoSiteRationalCertificate
public import proofs.PhosphorylationStableCapacity.TwoSiteSaddlePolynomialData
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

/-- One representative exact rational determinant evaluation. This pilot tests
trusted-kernel computation before any seven-point interpolation campaign. -/
theorem manuscriptTwoSiteA1_charpoly_eval_zero :
    manuscriptTwoSiteA1.charpoly.eval 0 = twoSiteSaddlePolyQ.eval 0 := by
  rw [Matrix.eval_charpoly]
  norm_num [twoSiteSaddlePolyQ]
  decide +kernel

theorem manuscriptTwoSiteA1_charpoly_eval_one :
    manuscriptTwoSiteA1.charpoly.eval 1 = twoSiteSaddlePolyQ.eval 1 := by
  rw [Matrix.eval_charpoly]
  norm_num [twoSiteSaddlePolyQ]
  decide +kernel

theorem manuscriptTwoSiteA1_charpoly_eval_two :
    manuscriptTwoSiteA1.charpoly.eval 2 = twoSiteSaddlePolyQ.eval 2 := by
  rw [Matrix.eval_charpoly]
  norm_num [twoSiteSaddlePolyQ]
  decide +kernel

theorem manuscriptTwoSiteA1_charpoly_eval_three :
    manuscriptTwoSiteA1.charpoly.eval 3 = twoSiteSaddlePolyQ.eval 3 := by
  rw [Matrix.eval_charpoly]
  norm_num [twoSiteSaddlePolyQ]
  decide +kernel

theorem manuscriptTwoSiteA1_charpoly_eval_four :
    manuscriptTwoSiteA1.charpoly.eval 4 = twoSiteSaddlePolyQ.eval 4 := by
  rw [Matrix.eval_charpoly]
  norm_num [twoSiteSaddlePolyQ]
  decide +kernel

theorem manuscriptTwoSiteA1_charpoly_eval_five :
    manuscriptTwoSiteA1.charpoly.eval 5 = twoSiteSaddlePolyQ.eval 5 := by
  rw [Matrix.eval_charpoly]
  norm_num [twoSiteSaddlePolyQ]
  decide +kernel

theorem manuscriptTwoSiteA1_charpoly_eval_six :
    manuscriptTwoSiteA1.charpoly.eval 6 = twoSiteSaddlePolyQ.eval 6 := by
  rw [Matrix.eval_charpoly]
  norm_num [twoSiteSaddlePolyQ]
  decide +kernel

end
end PhosphorylationStableCapacity
