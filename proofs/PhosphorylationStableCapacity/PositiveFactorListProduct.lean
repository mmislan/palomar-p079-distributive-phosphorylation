module
public import proofs.PhosphorylationStableCapacity.PositiveFactorProductLogConcavity

@[expose] public section

namespace PhosphorylationStableCapacity

open Polynomial

noncomputable section

theorem positiveFactorProduct_eq_list_prod (rs : List ℝ) :
    positiveFactorProduct rs = (rs.map fun r => X + C r).prod := by
  induction rs with
  | nil => simp [positiveFactorProduct]
  | cons r rs ih =>
      simp [positiveFactorProduct, positiveLinearStep_eq_mul, ih]

theorem coeffLogConcave_C_mul {p : ℝ[X]} {m : ℕ}
    (hp : CoeffLogConcave p m) (c : ℝ) :
    CoeffLogConcave (C c * p) m := by
  intro i hi0 him
  have h := hp i hi0 him
  simp only [coeff_C_mul]
  have hnonneg : 0 ≤ c ^ 2 *
      (p.coeff i ^ 2 - p.coeff (i - 1) * p.coeff (i + 1)) :=
    mul_nonneg (sq_nonneg c) (sub_nonneg.mpr h)
  nlinarith [hnonneg]

end
end PhosphorylationStableCapacity
