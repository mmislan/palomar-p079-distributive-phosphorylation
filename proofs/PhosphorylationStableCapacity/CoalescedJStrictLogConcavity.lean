module
public import proofs.PhosphorylationStableCapacity.NegativeRootStrictLogConcavity

@[expose] public section

namespace PhosphorylationStableCapacity

open Polynomial PhosphorylationSharpness

noncomputable section

/-- The literal companion source polynomial has strict coefficient
log-concavity at every interior index, uniformly in its length. -/
theorem coalescedJ_coeff_strict_logconcave (m : ℕ) :
    CoeffStrictLogConcave (coalescedPair m).2 m := by
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
  have hlead : 0 < (coalescedPair m).2.leadingCoeff := by
    rw [Polynomial.leadingCoeff, hd.degree_eq]
    exact hd.1 m le_rfl
  simpa [hd.degree_eq] using
    coeffStrictLogConcave_of_negative_roots hcard hneg hlead

/-- Adjacent preceding-coefficient ratios of the literal companion
polynomial are strictly increasing at its interior indices. -/
theorem coalescedJ_coeff_prev_ratio_strict (m i : ℕ)
    (hi : 0 < i) (him : i < m) :
    (coalescedPair m).2.coeff (i - 1) /
        (coalescedPair m).2.coeff i <
      (coalescedPair m).2.coeff i /
        (coalescedPair m).2.coeff (i + 1) := by
  have hd := (coalescedPair_dense m).2
  have hden0 := hd.1 i (by omega)
  have hden1 := hd.1 (i + 1) (by omega)
  apply (div_lt_div_iff₀ hden0 hden1).2
  simpa only [pow_two] using
    coalescedJ_coeff_strict_logconcave m i hi him

end
end PhosphorylationStableCapacity
