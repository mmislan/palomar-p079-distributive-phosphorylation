module
public import proofs.PhosphorylationStableCapacity.LoadedBindingDerivative

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section

/-- Recover a binding denominator from literal complex concentrations when
the free substrate concentrations are nonzero. -/
theorem bindingDenominator_ratio {ι : Type*} [Fintype ι]
    (S C : ι → ℝ) (hS : ∀ i, S i ≠ 0) :
    bindingDenominator (fun i => C i / S i) S = 1 + ∑ i, C i := by
  unfold bindingDenominator
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  exact div_mul_cancel₀ (C i) (hS i)

theorem bindingComplex_ratio {ι : Type*} [Fintype ι]
    (ET : ℝ) (S C : ι → ℝ) (hS : ∀ i, S i ≠ 0)
    (hET : ET = 1 + ∑ i, C i) (hET0 : ET ≠ 0) (i : ι) :
    bindingComplex ET (fun j => C j / S j) S i = C i := by
  unfold bindingComplex
  rw [bindingDenominator_ratio S C hS, ← hET]
  field_simp [hET0, hS i]

/-- At literal positive concentrations satisfying both enzyme totals,
the loaded mass formula is the binding-equilibrium inventory derivative. -/
theorem loadedBindingMass_hasDerivAt_from_concentrations
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ET FT : ℝ) (S C Y σ : ι → ℝ) (i : ι)
    (hS : ∀ j, S j ≠ 0)
    (hET : ET = 1 + ∑ j, C j)
    (hFT : FT = 1 + ∑ j, Y j)
    (hET0 : ET ≠ 0) (hFT0 : FT ≠ 0) :
    HasDerivAt (fun t : ℝ =>
      bindingLoadedLevel ET FT (fun j => C j / S j)
        (fun j => Y j / S j) (bindingLinearPath S σ t) i)
      ((loadedBindingMass S C Y ET FT).mulVec σ i) 0 := by
  have hp : bindingDenominator (fun j => C j / S j) S ≠ 0 := by
    rw [bindingDenominator_ratio S C hS, ← hET]
    exact hET0
  have hq : bindingDenominator (fun j => Y j / S j) S ≠ 0 := by
    rw [bindingDenominator_ratio S Y hS, ← hFT]
    exact hFT0
  have h := bindingLoadedLevel_hasDerivAt_linearPath ET FT
    (fun j => C j / S j) (fun j => Y j / S j) S σ i
    hET0 hFT0 hp hq
  have hC : bindingComplex ET (fun j => C j / S j) S = C := by
    funext j
    exact bindingComplex_ratio ET S C hS hET hET0 j
  have hY : bindingComplex FT (fun j => Y j / S j) S = Y := by
    funext j
    exact bindingComplex_ratio FT S Y hS hFT hFT0 j
  simpa only [hC, hY] using h

end
end PhosphorylationStableCapacity
