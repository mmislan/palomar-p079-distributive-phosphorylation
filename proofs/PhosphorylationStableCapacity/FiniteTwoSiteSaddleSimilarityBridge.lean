module
public import proofs.PhosphorylationStableCapacity.FiniteTwoSiteRationalCertificate
public import proofs.PhosphorylationStableCapacity.SaddleSimilarityBounds
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.NormNum

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section

def saddleA1Real : Matrix (Fin 6) (Fin 6) ℝ :=
  manuscriptTwoSiteA1.map (Rat.castHom ℝ)

/-- The exact scaled matrix in the saddle similarity certificate is the
printed middle equilibrium's proposed class Jacobian, entry by entry. -/
theorem saddleA1Real_eq_saddleA : saddleA1Real = saddleA.realMatrix := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [saddleA1Real, manuscriptTwoSiteA1, saddleA,
      ScaledIntegerMatrix.realMatrix]

theorem saddleBC_charpoly_eq_saddleA1Real :
    saddleBC.charpoly =
      (saddleA1Real.map (algebraMap ℝ ℂ)).charpoly := by
  rw [saddleBC_charpoly_eq_saddleAC, ← saddleA1Real_eq_saddleA]

theorem saddleA1Real_unique_right (z z' : ℂ)
    (hz : 0 ≤ z.re) (hz' : 0 ≤ z'.re)
    (hr : ((saddleA1Real.map (algebraMap ℝ ℂ)).charpoly).eval z = 0)
    (hr' : ((saddleA1Real.map (algebraMap ℝ ℂ)).charpoly).eval z' = 0) :
    z = z' := by
  apply saddleB_unique_right z z' hz hz'
  · rw [saddleBC_charpoly_eq_saddleA1Real]
    exact hr
  · rw [saddleBC_charpoly_eq_saddleA1Real]
    exact hr'

end
end PhosphorylationStableCapacity
