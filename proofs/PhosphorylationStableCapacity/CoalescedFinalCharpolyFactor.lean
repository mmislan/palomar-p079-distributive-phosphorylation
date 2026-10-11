module
public import proofs.PhosphorylationStableCapacity.FinalEdgeCharpolyFactor
public import proofs.PhosphorylationStableCapacity.CoalescedFinalCurrentWeight
public import proofs.PhosphorylationStableCapacity.CoalescedShearComplementHurwitz

@[expose] public section

namespace PhosphorylationStableCapacity

open Filter
open scoped Topology

noncomputable section

def coalescedFinalShearComplement (m : ℕ) (r τ : ℝ)
    (u : Fin (m + 2) → ℝ) : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ :=
  rankOneShearComplement
    (coalescedPrefixLoadedMatrix m r)
    (fun i : Fin (m + 1) => u i.castSucc)
    (fun j : Fin (m + 1) =>
      coalescedFullLoadedMatrix m r (Fin.last (m + 1)) j.castSucc) τ

/-- The literal final-current-weighted coalesced slow matrix has one exact
zero characteristic factor and the identified rank-one complement. -/
theorem coalescedFinalWeightedMatrix_charpoly_factor_of_kernel
    (m : ℕ) (r τ : ℝ) (u : Fin (m + 2) → ℝ)
    (hulast : u (Fin.last (m + 1)) = 1)
    (hKu : (coalescedFullLoadedMatrix m r).mulVec u = 0) :
    (coalescedFinalWeightedMatrix m r τ).charpoly =
      (coalescedFinalShearComplement m r τ u).charpoly *
        Polynomial.X := by
  have h := finalEdgeWeightedMatrix_charpoly_factor (m + 1)
    (coalescedFullLoadedMatrix m r) u hulast hKu τ
  have hweight : coalescedFinalWeightedMatrix m r τ =
      finalEdgeWeightedMatrix (m + 1)
        (coalescedFullLoadedMatrix m r) τ := by
    rfl
  have hcomp : finalEdgeShearComplement (m + 1)
      (coalescedFullLoadedMatrix m r) u τ =
        coalescedFinalShearComplement m r τ u := by
    ext i j
    simp [finalEdgeShearComplement, coalescedFinalShearComplement,
      rankOneShearComplement, coalescedFullLoadedMatrix_prefix]
  rw [← hweight, hcomp] at h
  exact h

/-- For large finite source parameter and final current weight near zero,
the exact weighted slow matrix has one zero characteristic factor and its
complementary factor is Hurwitz. -/
theorem coalescedFinalWeightedMatrix_eventually_hurwitz_complement (m : ℕ) :
    ∀ᶠ r : ℝ in atTop,
      ∃ u : Fin (m + 2) → ℝ,
        u (Fin.last (m + 1)) = 1 ∧
        (coalescedFullLoadedMatrix m r).mulVec u = 0 ∧
        ∀ᶠ τ : ℝ in 𝓝 (0 : ℝ),
          IsHurwitz (coalescedFinalShearComplement m r τ u) ∧
          (coalescedFinalWeightedMatrix m r τ).charpoly =
            (coalescedFinalShearComplement m r τ u).charpoly *
              Polynomial.X := by
  filter_upwards [coalescedShearComplement_eventually_hurwitz m]
    with r h
  obtain ⟨u, hulast, hKu, hhurwitz⟩ := h
  refine ⟨u, hulast, hKu, ?_⟩
  filter_upwards [hhurwitz] with τ hτ
  exact ⟨hτ, coalescedFinalWeightedMatrix_charpoly_factor_of_kernel
    m r τ u hulast hKu⟩

end
end PhosphorylationStableCapacity
