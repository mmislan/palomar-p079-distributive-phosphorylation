module
public import proofs.PhosphorylationStableCapacity.CoalescedWeightedSchurMatrixAction
public import proofs.PhosphorylationStableCapacity.CoalescedFiniteSlowSpectrum
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic

@[expose] public section

namespace PhosphorylationStableCapacity

open Filter
open scoped Topology

noncomputable section

/-- The physically realized current-row weighting and the previously
proved final-column weighting have exactly the same characteristic
polynomial, by the finite matrix `AB`/`BA` identity. -/
theorem coalescedWeightedCurrentMatrix_charpoly
    (m : ℕ) (r τ : ℝ) :
    ((Matrix.diagonal (coalescedFinalCurrentWeights m τ)) *
      (coalescedFullLoadedMatrix m r)).charpoly =
        (coalescedFinalWeightedMatrix m r τ).charpoly := by
  rw [Matrix.charpoly_mul_comm]
  rfl

/-- The finite matrix realized by a positive edge-retuned rate list has
one simple zero characteristic factor and a Hurwitz complementary factor
for small positive final weight. The separate weighted Schur intertwining
theorem docks this matrix to the literal slow Schur operator. -/
theorem coalescedWeightedCurrentSpectrum_eventually (m : ℕ) :
    ∀ᶠ r : ℝ in atTop,
      ∃ u : Fin (m + 2) → ℝ,
        u (Fin.last (m + 1)) = 1 ∧
        (coalescedFullLoadedMatrix m r).mulVec u = 0 ∧
        ∀ᶠ τ : ℝ in 𝓝[>] (0 : ℝ),
          0 < τ ∧
          IsHurwitz (coalescedFinalShearComplement m r τ u) ∧
          (coalescedFinalShearComplement m r τ u).charpoly.eval 0 ≠ 0 ∧
          ((Matrix.diagonal (coalescedFinalCurrentWeights m τ)) *
            (coalescedFullLoadedMatrix m r)).charpoly =
              (coalescedFinalShearComplement m r τ u).charpoly *
                Polynomial.X := by
  filter_upwards [coalescedFiniteSlowSpectrum_eventually m]
    with r hsource
  obtain ⟨u, hulast, hKu, hnear⟩ := hsource
  refine ⟨u, hulast, hKu, ?_⟩
  filter_upwards [hnear] with τ hτ
  obtain ⟨hpos, hhurwitz, hzero, hchar⟩ := hτ
  refine ⟨hpos, hhurwitz, hzero, ?_⟩
  rw [coalescedWeightedCurrentMatrix_charpoly, hchar]

end
end PhosphorylationStableCapacity
