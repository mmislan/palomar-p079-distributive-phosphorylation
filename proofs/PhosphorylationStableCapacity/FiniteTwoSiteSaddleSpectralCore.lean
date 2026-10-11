module
public import proofs.PhosphorylationStableCapacity.FiniteTwoSiteSaddleCharpoly
public import proofs.PhosphorylationStableCapacity.FiniteTwoSiteSaddleSimilarityBridge
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section

theorem saddleA1Real_charpoly :
    saddleA1Real.charpoly = twoSiteSaddlePolyR := by
  rw [saddleA1Real, Matrix.charpoly_map, manuscriptTwoSiteA1_charpoly]
  rfl

theorem saddleA1Real_positive_simple_root :
    ∃ x : ℝ, 0 < x ∧ saddleA1Real.charpoly.IsRoot x ∧
      ((saddleA1Real.map (algebraMap ℝ ℂ)).charpoly).derivative.eval
        (x : ℂ) ≠ 0 := by
  obtain ⟨x, hx, _hx1, hroot⟩ := twoSiteSaddlePolyR_exists_positive_root
  refine ⟨x, hx, ?_, ?_⟩
  · simpa [saddleA1Real_charpoly, Polynomial.IsRoot] using hroot
  · have hd : twoSiteSaddlePolyR.derivative.eval x ≠ 0 :=
      ne_of_gt (twoSiteSaddlePolyR_derivative_pos hx.le)
    rw [Matrix.charpoly_map, saddleA1Real_charpoly,
      Polynomial.derivative_map]
    have hmap :
        (twoSiteSaddlePolyR.derivative.map (algebraMap ℝ ℂ)).eval (x : ℂ) =
          ((twoSiteSaddlePolyR.derivative.eval x : ℝ) : ℂ) := by
      simpa using (Polynomial.eval_map_apply
        (p := twoSiteSaddlePolyR.derivative) (f := algebraMap ℝ ℂ) x)
    rw [hmap]
    exact_mod_cast hd

theorem saddleA1Real_one_unstable :
    ∃ x : ℝ, 0 < x ∧ saddleA1Real.charpoly.IsRoot x ∧
      ((saddleA1Real.map (algebraMap ℝ ℂ)).charpoly).derivative.eval
        (x : ℂ) ≠ 0 ∧
      ∀ z : ℂ,
        z ∈ spectrum ℂ (saddleA1Real.map (algebraMap ℝ ℂ)) →
        z.re < 0 ∨ z = (x : ℂ) := by
  obtain ⟨x, hx, hr, hd⟩ := saddleA1Real_positive_simple_root
  refine ⟨x, hx, hr, hd, ?_⟩
  intro z hz
  by_cases hneg : z.re < 0
  · exact Or.inl hneg
  · right
    apply saddleA1Real_unique_right z (x : ℂ)
      (le_of_not_gt hneg) (by exact_mod_cast hx.le)
    · exact Matrix.mem_spectrum_iff_isRoot_charpoly.mp hz
    · rw [Matrix.charpoly_map, saddleA1Real_charpoly]
      have hmap :
          (twoSiteSaddlePolyR.map (algebraMap ℝ ℂ)).eval (x : ℂ) =
            ((twoSiteSaddlePolyR.eval x : ℝ) : ℂ) := by
        simpa using (Polynomial.eval_map_apply
          (p := twoSiteSaddlePolyR) (f := algebraMap ℝ ℂ) x)
      rw [hmap]
      have hreal : twoSiteSaddlePolyR.eval x = 0 := by
        simpa [saddleA1Real_charpoly, Polynomial.IsRoot] using hr
      exact_mod_cast hreal

end
end PhosphorylationStableCapacity
