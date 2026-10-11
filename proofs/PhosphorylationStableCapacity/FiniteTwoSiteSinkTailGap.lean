module
public import proofs.PhosphorylationStableCapacity.FiniteTwoSiteTailPositiveRoot
public import proofs.PhosphorylationStableCapacity.FiniteTwoSiteTailSmallGain
public import proofs.PhosphorylationStableCapacity.FiniteTwoSiteSink0Spectral
public import proofs.PhosphorylationStableCapacity.FiniteTwoSiteSink2Spectral
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs

@[expose] public section
set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

namespace PhosphorylationStableCapacity

noncomputable section

private theorem twoSiteTailBC0_charpoly_eq_A :
    twoSiteTailBC0.charpoly =
      (twoSiteTailA0.realMatrix.map (algebraMap ℝ ℂ)).charpoly := by
  rw [twoSiteTailBC0, Matrix.charpoly_map,
    twoSiteTailB0_charpoly_eq_A, ← Matrix.charpoly_map]

private theorem twoSiteTailBC2_charpoly_eq_A :
    twoSiteTailBC2.charpoly =
      (twoSiteTailA2.realMatrix.map (algebraMap ℝ ℂ)).charpoly := by
  rw [twoSiteTailBC2, Matrix.charpoly_map,
    twoSiteTailB2_charpoly_eq_A, ← Matrix.charpoly_map]

/-- The first printed two-site sink has exactly one characteristic root
with real part at least `-2`; it is real, simple, and lies in `(-2,0)`.
Every other characteristic root has real part below `-2`. -/
theorem twoSiteTailA0_sink_gap :
    ∃ x : ℝ, -2 < x ∧ x < 0 ∧
      twoSiteTailA0.realMatrix.charpoly.IsRoot x ∧
      ((twoSiteTailA0.realMatrix.map (algebraMap ℝ ℂ)).charpoly).derivative.eval
        (x : ℂ) ≠ 0 ∧
      ∀ z : ℂ,
        z ∈ spectrum ℂ (twoSiteTailA0.realMatrix.map (algebraMap ℝ ℂ)) →
        z.re < -2 ∨ z = (x : ℂ) := by
  obtain ⟨x, hx, hr⟩ := twoSiteTailA0_exists_root_above_neg_two
  have hrootBC : twoSiteTailBC0.charpoly.eval (x : ℂ) = 0 := by
    rw [twoSiteTailBC0_charpoly_eq_A, Matrix.charpoly_map]
    have hmap :
        (twoSiteTailA0.realMatrix.charpoly.map (algebraMap ℝ ℂ)).eval (x : ℂ) =
          ((twoSiteTailA0.realMatrix.charpoly.eval x : ℝ) : ℂ) := by
      simpa using Polynomial.eval_map_apply
        (p := twoSiteTailA0.realMatrix.charpoly) (f := algebraMap ℝ ℂ) x
    rw [hmap]
    exact_mod_cast hr
  have hmatrix : twoSiteTailA0.realMatrix = twoSiteA0Real := by
    simpa only [twoSiteA0Real, Rat.coe_castHom] using twoSiteTailA0_literal
  have hxneg : x < 0 := by
    have h := twoSiteA0Real_hurwitz (x : ℂ) (by
      simpa only [twoSiteTailBC0_charpoly_eq_A, hmatrix] using hrootBC)
    simpa using h
  have hsimple := twoSiteTailBC0_simple_above_neg_two (x : ℂ)
    (by exact_mod_cast hx.le) hrootBC
  refine ⟨x, hx, hxneg, by simpa [Polynomial.IsRoot] using hr,
    by simpa only [twoSiteTailBC0_charpoly_eq_A] using hsimple, ?_⟩
  intro z hz
  by_cases hleft : z.re < -2
  · exact Or.inl hleft
  right
  apply twoSiteTailBC0_unique_above_neg_two z (x : ℂ)
    (le_of_not_gt hleft) (by exact_mod_cast hx.le)
  · rw [twoSiteTailBC0_charpoly_eq_A]
    exact Matrix.mem_spectrum_iff_isRoot_charpoly.mp hz
  · exact hrootBC

theorem twoSiteTailA2_sink_gap :
    ∃ x : ℝ, -2 < x ∧ x < 0 ∧
      twoSiteTailA2.realMatrix.charpoly.IsRoot x ∧
      ((twoSiteTailA2.realMatrix.map (algebraMap ℝ ℂ)).charpoly).derivative.eval
        (x : ℂ) ≠ 0 ∧
      ∀ z : ℂ,
        z ∈ spectrum ℂ (twoSiteTailA2.realMatrix.map (algebraMap ℝ ℂ)) →
        z.re < -2 ∨ z = (x : ℂ) := by
  obtain ⟨x, hx, hr⟩ := twoSiteTailA2_exists_root_above_neg_two
  have hrootBC : twoSiteTailBC2.charpoly.eval (x : ℂ) = 0 := by
    rw [twoSiteTailBC2_charpoly_eq_A, Matrix.charpoly_map]
    have hmap :
        (twoSiteTailA2.realMatrix.charpoly.map (algebraMap ℝ ℂ)).eval (x : ℂ) =
          ((twoSiteTailA2.realMatrix.charpoly.eval x : ℝ) : ℂ) := by
      simpa using Polynomial.eval_map_apply
        (p := twoSiteTailA2.realMatrix.charpoly) (f := algebraMap ℝ ℂ) x
    rw [hmap]
    exact_mod_cast hr
  have hmatrix : twoSiteTailA2.realMatrix = twoSiteA2Real := by
    simpa only [twoSiteA2Real, Rat.coe_castHom] using twoSiteTailA2_literal
  have hxneg : x < 0 := by
    have h := twoSiteA2Real_hurwitz (x : ℂ) (by
      simpa only [twoSiteTailBC2_charpoly_eq_A, hmatrix] using hrootBC)
    simpa using h
  have hsimple := twoSiteTailBC2_simple_above_neg_two (x : ℂ)
    (by exact_mod_cast hx.le) hrootBC
  refine ⟨x, hx, hxneg, by simpa [Polynomial.IsRoot] using hr,
    by simpa only [twoSiteTailBC2_charpoly_eq_A] using hsimple, ?_⟩
  intro z hz
  by_cases hleft : z.re < -2
  · exact Or.inl hleft
  right
  apply twoSiteTailBC2_unique_above_neg_two z (x : ℂ)
    (le_of_not_gt hleft) (by exact_mod_cast hx.le)
  · rw [twoSiteTailBC2_charpoly_eq_A]
    exact Matrix.mem_spectrum_iff_isRoot_charpoly.mp hz
  · exact hrootBC

end
end PhosphorylationStableCapacity
