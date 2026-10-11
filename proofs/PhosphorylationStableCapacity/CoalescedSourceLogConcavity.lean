module
public import proofs.PhosphorylationStableCapacity.NegativeRootLogConcavity

@[expose] public section

namespace PhosphorylationStableCapacity

open Polynomial PhosphorylationSharpness

noncomputable section

theorem coalescedN_coeff_logconcave (m : ℕ) :
    CoeffLogConcave (coalescedPair m).1 m := by
  have hd := (coalescedPair_dense m).1
  have hcard : (coalescedPair m).1.roots.card =
      (coalescedPair m).1.natDegree := by
    rw [coalescedN_roots_eq]
    simpa [coalescedRootSet_card] using hd.degree_eq.symm
  have hneg : ∀ r ∈ (coalescedPair m).1.roots, r < 0 := by
    intro r hr
    rw [coalescedN_roots_eq] at hr
    have hr' : r ∈ (Finset.range m).image (coalescedRoot m) := by
      simpa [coalescedRootSet] using hr
    rcases Finset.mem_image.mp hr' with ⟨j, hj, rfl⟩
    exact coalescedRoot_neg m j (Finset.mem_range.mp hj)
  simpa [hd.degree_eq] using
    coeffLogConcave_of_negative_roots hcard hneg

theorem coalescedJ_coeff_logconcave (m : ℕ) :
    CoeffLogConcave (coalescedPair m).2 m := by
  have hd := (coalescedPair_dense m).2
  have hcard : (coalescedPair m).2.roots.card =
      (coalescedPair m).2.natDegree := by
    rw [coalescedJ_roots_eq]
    simpa [coalescedJRootSet_card] using hd.degree_eq.symm
  have hneg : ∀ r ∈ (coalescedPair m).2.roots, r < 0 := by
    intro r hr
    rw [coalescedJ_roots_eq] at hr
    have hr' : r ∈ Finset.univ.image (coalescedJRoot m) := by
      simpa [coalescedJRootSet] using hr
    rcases Finset.mem_image.mp hr' with ⟨j, _, rfl⟩
    exact coalescedJRoot_neg m j
  simpa [hd.degree_eq] using
    coeffLogConcave_of_negative_roots hcard hneg

end
end PhosphorylationStableCapacity
