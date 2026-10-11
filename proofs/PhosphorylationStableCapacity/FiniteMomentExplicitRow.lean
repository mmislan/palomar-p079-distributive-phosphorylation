module
public import proofs.PhosphorylationStableCapacity.SourceAugmentedRankOne
public import proofs.PhosphorylationStableCapacity.LoadedBindingTotalPivot

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section
open PhosphorylationSharpness Matrix

/-- The all-size augmented total row has a direct physical coordinate
formula. It removes an `(n+1)×(n+1)` matrix expansion from each finite
moment certificate. -/
theorem sourceAugmentedTotalRow_eq_physical {n : ℕ}
    (x : State n) (hx : x.Positive) (j : Fin (n+1)) :
    sourceAugmentedTotalRow x j = x.S j +
      sourceLevelC x j * x.E / totalE x +
      sourceLevelD x j * x.F / totalF x := by
  have hET : 0 < totalE x := by
    simp [totalE]
    exact add_pos_of_pos_of_nonneg hx.2.1
      (Finset.sum_nonneg fun i _ => (hx.2.2.2.1 i).le)
  have hFT : 0 < totalF x := by
    simp [totalF]
    exact add_pos_of_pos_of_nonneg hx.2.2.1
      (Finset.sum_nonneg fun i _ => (hx.2.2.2.2 i).le)
  have h := loadedBindingMass_column_sum_general
    x.S (sourceLevelC x) (sourceLevelD x)
    (totalE x) (totalF x) x.E x.F
    (by simp [totalE, sourceLevelC_sum])
    (by simp [totalF, sourceLevelD_sum])
    (ne_of_gt hET) (ne_of_gt hFT) j
  simpa [sourceAugmentedTotalRow, totalAndLevelOutputMatrix,
    Matrix.mul_apply] using h

end
end PhosphorylationStableCapacity
