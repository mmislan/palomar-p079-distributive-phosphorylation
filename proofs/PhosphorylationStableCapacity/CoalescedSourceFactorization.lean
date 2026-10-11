module
public import proofs.PhosphorylationStableCapacity.CoalescedFactorMatching

@[expose] public section

namespace PhosphorylationStableCapacity

open Polynomial PhosphorylationSharpness

noncomputable section

/-- Exact factorization of the source numerator by its explicit, distinct
negative real roots. -/
theorem coalescedN_factorization (m : ℕ) :
    C (coalescedPair m).1.leadingCoeff *
        ((coalescedRootSet m).val.map fun r : ℝ => X - C r).prod =
      (coalescedPair m).1 := by
  have hcard : (coalescedPair m).1.roots.card =
      (coalescedPair m).1.natDegree := by
    rw [coalescedN_roots_eq]
    simpa [coalescedRootSet_card] using
      (coalescedPair_dense m).1.degree_eq.symm
  simpa only [coalescedN_roots_eq] using
    Polynomial.C_leadingCoeff_mul_prod_multiset_X_sub_C hcard

/-- Exact companion factorization by the interlacing negative real roots. -/
theorem coalescedJ_factorization (m : ℕ) :
    C (coalescedPair m).2.leadingCoeff *
        ((coalescedJRootSet m).val.map fun r : ℝ => X - C r).prod =
      (coalescedPair m).2 := by
  have hcard : (coalescedPair m).2.roots.card =
      (coalescedPair m).2.natDegree := by
    rw [coalescedJ_roots_eq]
    simpa [coalescedJRootSet_card] using
      (coalescedPair_dense m).2.degree_eq.symm
  simpa only [coalescedJ_roots_eq] using
    Polynomial.C_leadingCoeff_mul_prod_multiset_X_sub_C hcard

end
end PhosphorylationStableCapacity
