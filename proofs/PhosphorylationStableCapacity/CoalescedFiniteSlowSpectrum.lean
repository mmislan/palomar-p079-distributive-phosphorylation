module
public import proofs.PhosphorylationStableCapacity.CoalescedFinalCharpolyFactor
public import proofs.PhosphorylationStableCapacity.HurwitzCharpolyZero

@[expose] public section

namespace PhosphorylationStableCapacity

open Filter
open scoped Topology

noncomputable section

/-- With a sufficiently large finite source parameter and sufficiently
small positive final current weight, the exact loaded slow matrix has one
algebraically simple zero and a Hurwitz complementary characteristic
factor. This is the finite slow subsystem, not the full class Jacobian. -/
theorem coalescedFiniteSlowSpectrum_eventually (m : ℕ) :
    ∀ᶠ r : ℝ in atTop,
      ∃ u : Fin (m + 2) → ℝ,
        u (Fin.last (m + 1)) = 1 ∧
        (coalescedFullLoadedMatrix m r).mulVec u = 0 ∧
        ∀ᶠ τ : ℝ in 𝓝[>] (0 : ℝ),
          0 < τ ∧
          IsHurwitz (coalescedFinalShearComplement m r τ u) ∧
          (coalescedFinalShearComplement m r τ u).charpoly.eval 0 ≠ 0 ∧
          (coalescedFinalWeightedMatrix m r τ).charpoly =
            (coalescedFinalShearComplement m r τ u).charpoly *
              Polynomial.X := by
  filter_upwards [coalescedFinalWeightedMatrix_eventually_hurwitz_complement m]
    with r h
  obtain ⟨u, hulast, hKu, hnear⟩ := h
  refine ⟨u, hulast, hKu, ?_⟩
  filter_upwards [self_mem_nhdsWithin,
    hnear.filter_mono nhdsWithin_le_nhds] with τ hpos hτ
  exact ⟨hpos, hτ.1,
    isHurwitz_charpoly_eval_zero_ne_zero hτ.1, hτ.2⟩

end
end PhosphorylationStableCapacity
