module
public import proofs.PhosphorylationStableCapacity.SplitJacobianContinuity

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section

open Matrix Polynomial Filter
open scoped Topology

/-- The complex simple-zero spectral certificate has an exact real
characteristic-polynomial consequence: its linear coefficient is nonzero. -/
theorem simpleNeutral_real_charpoly_coeff_one_ne_zero
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι ℝ)
    (hM : SimpleNeutralHurwitzComplement M) :
    M.charpoly.coeff 1 ≠ 0 := by
  obtain ⟨p, hfactor, hp, _⟩ := hM
  have hc : ((M.map (algebraMap ℝ ℂ)).charpoly).coeff 1 ≠ 0 := by
    rw [hfactor, Polynomial.coeff_X_mul]
    simpa only [Polynomial.coeff_zero_eq_eval_zero] using hp
  rw [Matrix.charpoly_map, Polynomial.coeff_map] at hc
  exact fun h => hc (by simp [h])

/-- The same certificate gives a real zero constant coefficient. -/
theorem simpleNeutral_real_charpoly_coeff_zero
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι ℝ)
    (hM : SimpleNeutralHurwitzComplement M) :
    M.charpoly.coeff 0 = 0 := by
  obtain ⟨p, hfactor, _, _⟩ := hM
  have hc : ((M.map (algebraMap ℝ ℂ)).charpoly).coeff 0 = 0 := by
    rw [hfactor, Polynomial.coeff_zero_eq_eval_zero]
    simp
  rw [Matrix.charpoly_map, Polynomial.coeff_map] at hc
  exact Complex.ofReal_injective (by simpa using hc)

theorem simpleNeutral_real_charpoly_derivative_nonzero
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι ℝ)
    (hM : SimpleNeutralHurwitzComplement M) :
    M.charpoly.derivative.eval 0 ≠ 0 := by
  have h := simpleNeutral_real_charpoly_coeff_one_ne_zero M hM
  simpa [← Polynomial.coeff_zero_eq_eval_zero,
    Polynomial.coeff_derivative] using h

end
end PhosphorylationStableCapacity
