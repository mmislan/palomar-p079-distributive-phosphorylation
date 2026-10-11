module
public import proofs.PhosphorylationStableCapacity.CoalescedNormalizedKernel
public import proofs.PhosphorylationStableCapacity.CoalescedPrefixStrictCertificate
public import proofs.PhosphorylationStableCapacity.RankOneMetzlerPerturbation

@[expose] public section

namespace PhosphorylationStableCapacity

open Filter
open scoped Topology

noncomputable section

/-- At sufficiently large coalesced source parameters, the complementary
rank-one block associated with a normalized zero mode is Hurwitz for final
current weight near zero. Its identification with the full weighted matrix
still requires the triangular similarity identity. -/
theorem coalescedShearComplement_eventually_hurwitz (m : ℕ) :
    ∀ᶠ r : ℝ in atTop,
      ∃ u : Fin (m + 2) → ℝ,
        u (Fin.last (m + 1)) = 1 ∧
        (coalescedFullLoadedMatrix m r).mulVec u = 0 ∧
        ∀ᶠ τ : ℝ in 𝓝 (0 : ℝ),
          IsHurwitz (rankOneShearComplement
            (coalescedPrefixLoadedMatrix m r)
            (fun i : Fin (m + 1) => u i.castSucc)
            (fun j : Fin (m + 1) =>
              coalescedFullLoadedMatrix m r (Fin.last (m + 1)) j.castSucc)
            τ) := by
  filter_upwards [coalescedFullLoadedMatrix_eventually_normalized_kernel m,
    coalescedPrefixLoadedMatrix_eventually_strict_certificate m]
    with r hkernel hcert
  obtain ⟨u, hulast, hKu⟩ := hkernel
  refine ⟨u, hulast, hKu, ?_⟩
  exact rankOneShearComplement_eventually_hurwitz
    (coalescedPrefixLoadedMatrix m r)
    (fun i : Fin (m + 1) => u i.castSucc)
    (fun j : Fin (m + 1) =>
      coalescedFullLoadedMatrix m r (Fin.last (m + 1)) j.castSucc)
    (pathVectorFin (coalescedPathWeights m))
    (pathVectorFin_pos (coalescedPathWeights m)
      (coalescedPathWeights_pos m)) hcert.1 hcert.2

end
end PhosphorylationStableCapacity
