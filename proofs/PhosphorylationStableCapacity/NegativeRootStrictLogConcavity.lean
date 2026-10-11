module
public import proofs.PhosphorylationStableCapacity.PositiveFactorStrictLogConcavity

@[expose] public section

namespace PhosphorylationStableCapacity

open Polynomial

noncomputable section

theorem coeffStrictLogConcave_C_mul {p : ℝ[X]} {m : ℕ}
    (hp : CoeffStrictLogConcave p m) (c : ℝ) (hc : 0 < c) :
    CoeffStrictLogConcave (C c * p) m := by
  intro i hi0 him
  have h := hp i hi0 him
  simp only [coeff_C_mul]
  have hpos : 0 < c ^ 2 *
      (p.coeff i ^ 2 - p.coeff (i - 1) * p.coeff (i + 1)) :=
    mul_pos (pow_pos hc _) (sub_pos.mpr h)
  nlinarith [hpos]

/-- A positive-leading-coefficient polynomial whose complete roots are
negative has strictly log-concave interior coefficients. -/
theorem coeffStrictLogConcave_of_negative_roots {p : ℝ[X]}
    (hcard : p.roots.card = p.natDegree)
    (hneg : ∀ r ∈ p.roots, r < 0)
    (hlead : 0 < p.leadingCoeff) :
    CoeffStrictLogConcave p p.natDegree := by
  have hpos := negativeRootFactorList_pos p.roots hneg
  have hlc := positiveFactorProduct_strictLogConcave
    (negativeRootFactorList p.roots) hpos
  rw [negativeRootFactorList_length, hcard] at hlc
  have hfac := Polynomial.C_leadingCoeff_mul_prod_multiset_X_sub_C hcard
  rw [← negativeRootFactorList_prod] at hfac
  have hscaled := coeffStrictLogConcave_C_mul hlc p.leadingCoeff hlead
  rw [hfac] at hscaled
  exact hscaled

end
end PhosphorylationStableCapacity
