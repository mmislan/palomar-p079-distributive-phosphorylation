module
public import proofs.PhosphorylationStableCapacity.FiniteTwoSiteSinkTailGap
public import proofs.PhosphorylationStableCapacity.FiniteTwoSiteSaddleTailGap
public import proofs.PhosphorylationStableCapacity.FiniteTwoSiteJacobianBridge
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Linarith

@[expose] public section
set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

namespace PhosphorylationStableCapacity

noncomputable section
open PhosphorylationSharpness

/-- The quantitative clause in the manuscript's printed two-site example:
one simple dominant real root and all five remaining roots left of `-2`. -/
def OneDominantTailGap {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) : Prop :=
  ∃ x : ℝ, -2 < x ∧ A.charpoly.IsRoot x ∧
    ((A.map (algebraMap ℝ ℂ)).charpoly).derivative.eval (x : ℂ) ≠ 0 ∧
    ∀ z : ℂ, z ∈ spectrum ℂ (A.map (algebraMap ℝ ℂ)) →
      z.re < -2 ∨ z = (x : ℂ)

private theorem oneDominantTailGap_of_charpoly_eq
    {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ]
    (A : Matrix ι ι ℝ) (B : Matrix κ κ ℝ)
    (hchar : A.charpoly = B.charpoly) (hB : OneDominantTailGap B) :
    OneDominantTailGap A := by
  obtain ⟨x, hx, hr, hd, hrest⟩ := hB
  refine ⟨x, hx, ?_, ?_, ?_⟩
  · simpa only [hchar] using hr
  · simpa only [Matrix.charpoly_map, hchar] using hd
  · intro z hz
    have hzB : z ∈ spectrum ℂ (B.map (algebraMap ℝ ℂ)) := by
      apply Matrix.mem_spectrum_iff_isRoot_charpoly.mpr
      have hzr := Matrix.mem_spectrum_iff_isRoot_charpoly.mp hz
      simpa only [Matrix.charpoly_map, hchar] using hzr
    exact hrest z hzB

private theorem twoSiteTailA0_property : OneDominantTailGap twoSiteTailA0.realMatrix := by
  obtain ⟨x, hx, _hx0, hr, hd, hrest⟩ := twoSiteTailA0_sink_gap
  exact ⟨x, hx, hr, hd, hrest⟩

private theorem twoSiteTailA2_property : OneDominantTailGap twoSiteTailA2.realMatrix := by
  obtain ⟨x, hx, _hx0, hr, hd, hrest⟩ := twoSiteTailA2_sink_gap
  exact ⟨x, hx, hr, hd, hrest⟩

private theorem twoSiteTailA1_property : OneDominantTailGap saddleA1Real := by
  obtain ⟨x, hx, hr, hd, hrest⟩ := saddleA1Real_tail_gap
  exact ⟨x, by linarith, hr, hd, hrest⟩

private theorem manuscriptTwoSiteMatrixFin_zero_tail_gap :
    OneDominantTailGap (manuscriptTwoSiteMatrixFin 0) := by
  apply oneDominantTailGap_of_charpoly_eq
    (manuscriptTwoSiteMatrixFin 0) twoSiteTailA0.realMatrix
  · rw [manuscriptTwoSiteMatrixFin_zero_eq,
      twoSiteA0Real, twoSiteTailA0_literal]
    simp only [Rat.coe_castHom]
  · exact twoSiteTailA0_property

private theorem manuscriptTwoSiteMatrixFin_one_tail_gap :
    OneDominantTailGap (manuscriptTwoSiteMatrixFin 1) := by
  apply oneDominantTailGap_of_charpoly_eq
    (manuscriptTwoSiteMatrixFin 1) saddleA1Real
  · rw [manuscriptTwoSiteMatrixFin_one_eq]
    rfl
  · exact twoSiteTailA1_property

private theorem manuscriptTwoSiteMatrixFin_two_tail_gap :
    OneDominantTailGap (manuscriptTwoSiteMatrixFin 2) := by
  apply oneDominantTailGap_of_charpoly_eq
    (manuscriptTwoSiteMatrixFin 2) twoSiteTailA2.realMatrix
  · rw [manuscriptTwoSiteMatrixFin_two_eq,
      twoSiteA2Real, twoSiteTailA2_literal]
    simp only [Rat.coe_castHom]
  · exact twoSiteTailA2_property

theorem manuscriptTwoSiteMatrixFin_all_tail_gap (j : Fin 3) :
    OneDominantTailGap (manuscriptTwoSiteMatrixFin j) := by
  fin_cases j
  · exact manuscriptTwoSiteMatrixFin_zero_tail_gap
  · exact manuscriptTwoSiteMatrixFin_one_tail_gap
  · exact manuscriptTwoSiteMatrixFin_two_tail_gap

/-- The `-2` tail bound is attached to the actual restricted mass-action
Jacobian at each printed two-site equilibrium, not just to certificate data. -/
theorem manuscriptTwoSite_literal_all_tail_gap (j : Fin 3) :
    OneDominantTailGap
      (restrictedJacobianMatrix 4 2 6 manuscriptTwoSiteRates
        (toCoordinateSpace (chart (manuscriptTwoSiteStates j)))) := by
  apply oneDominantTailGap_of_charpoly_eq _
    (manuscriptTwoSiteMatrixFin j)
  · rw [manuscriptTwoSiteMatrixFin]
    exact (Matrix.charpoly_reindex _ _).symm
  · exact manuscriptTwoSiteMatrixFin_all_tail_gap j

end
end PhosphorylationStableCapacity
