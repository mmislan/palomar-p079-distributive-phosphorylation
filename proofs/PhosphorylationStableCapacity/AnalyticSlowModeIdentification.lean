module
public import proofs.PhosphorylationStableCapacity.AnalyticPolynomialSlowBranch
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs
public import Mathlib.Analysis.Complex.Basic

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section

open Matrix Polynomial

/-- A real characteristic root near zero is the already selected slow mode
when every other eigenvalue lies to the left of a fixed negative margin. -/
theorem near_real_root_eq_selected_transverse_mode
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (J : Matrix ι ι ℝ) (α lamSelected lamNear : ℝ)
    (hnear : -α < lamNear)
    (hroot : J.charpoly.IsRoot lamNear)
    (hmargin : ∀ z : ℂ,
      z ∈ spectrum ℂ (J.map (algebraMap ℝ ℂ)) →
        z = (lamSelected : ℂ) ∨ z.re ≤ -α) :
    lamNear = lamSelected := by
  have hspectrum : (lamNear : ℂ) ∈
      spectrum ℂ (J.map (algebraMap ℝ ℂ)) := by
    apply Matrix.mem_spectrum_iff_isRoot_charpoly.mpr
    simpa only [Matrix.charpoly_map, ← Complex.coe_algebraMap] using
      (Polynomial.IsRoot.map (f := algebraMap ℝ ℂ) hroot)
  rcases hmargin (lamNear : ℂ) hspectrum with heq | hleft
  · exact_mod_cast heq
  · have hre : (lamNear : ℂ).re = lamNear := by simp
    linarith

end
end PhosphorylationStableCapacity
