module
public import proofs.PhosphorylationStableCapacity.LoadedBindingModeRows

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section

/-- The column sum is the coefficient of that substrate's variation in
the total loaded-inventory derivative. -/
theorem loadedBindingMass_column_sum {ι : Type*}
    [Fintype ι] [DecidableEq ι]
    (S C Y : ι → ℝ) (ET FT : ℝ)
    (hET : ET = 1 + ∑ i, C i)
    (hFT : FT = 1 + ∑ i, Y i)
    (hETne : ET ≠ 0) (hFTne : FT ≠ 0)
    (j : ι) :
    (∑ i, loadedBindingMass S C Y ET FT i j) =
      S j + C j / ET + Y j / FT := by
  let σ : ι → ℝ := fun i => if i = j then 1 else 0
  have h := loadedBindingMass_total_action S C Y σ ET FT
    hET hFT hETne hFTne
  simpa [σ, Matrix.mulVec, dotProduct] using h

end
end PhosphorylationStableCapacity
