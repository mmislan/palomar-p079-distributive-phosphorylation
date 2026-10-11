module
public import proofs.PhosphorylationStableCapacity.LoadedBindingAlgebra

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section

/-! Exact mode-row identities for the loaded binding mass matrix. The
finite-dimensional pilot used positive `S`, nonnegative `C,Y`, exact totals
`ET=1+sum C`, `FT=1+sum Y`, and `C` zero and `S=Y` on the final level.
These identities do not assume or prove an asymptotic inverse limit. -/

/-- The total row of the loaded mass matrix retains one free-enzyme share
of each family of complex variation. -/
theorem loadedBindingMass_total_action {ι : Type*}
    [Fintype ι] [DecidableEq ι]
    (S C Y σ : ι → ℝ) (ET FT : ℝ)
    (hET : ET = 1 + ∑ i, C i)
    (hFT : FT = 1 + ∑ i, Y i)
    (hETne : ET ≠ 0) (hFTne : FT ≠ 0) :
    (∑ i, (loadedBindingMass S C Y ET FT).mulVec σ i) =
      (∑ i, S i * σ i) +
        (∑ i, C i * σ i) / ET +
          (∑ i, Y i * σ i) / FT := by
  simp_rw [loadedBindingMass_action, mul_sub]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  rw [← Finset.sum_mul, ← Finset.sum_mul]
  have hC :
      (∑ i, C i * σ i) -
        (∑ i, C i) * ((∑ i, C i * σ i) / ET) =
          (∑ i, C i * σ i) / ET := by
    field_simp [hETne]
    rw [hET]
    ring
  have hY :
      (∑ i, Y i * σ i) -
        (∑ i, Y i) * ((∑ i, Y i * σ i) / FT) =
          (∑ i, Y i * σ i) / FT := by
    field_simp [hFTne]
    rw [hFT]
    ring
  linarith [hC, hY]

/-- If the final level carries no kinase complex and its free substrate
equals its phosphatase complex, its mass row has a two-term form. -/
theorem loadedBindingMass_final_action {ι : Type*}
    [Fintype ι] [DecidableEq ι]
    (S C Y σ : ι → ℝ) (ET FT : ℝ) (last : ι)
    (hC : C last = 0) (hS : S last = Y last) :
    (loadedBindingMass S C Y ET FT).mulVec σ last =
      Y last * (2 * σ last - (∑ i, Y i * σ i) / FT) := by
  rw [loadedBindingMass_action]
  rw [hC, hS]
  ring

/-- With phosphatase total two, a zero final mass row fixes the weighted
phosphatase response to four times the final log-substrate response. -/
theorem loadedBindingMass_final_zero_equation {ι : Type*}
    [Fintype ι] [DecidableEq ι]
    (S C Y σ : ι → ℝ) (ET : ℝ) (last : ι)
    (hC : C last = 0) (hS : S last = Y last)
    (hY : Y last ≠ 0)
    (hzero : (loadedBindingMass S C Y ET 2).mulVec σ last = 0) :
    (∑ i, Y i * σ i) = 4 * σ last := by
  rw [loadedBindingMass_final_action S C Y σ ET 2 last hC hS] at hzero
  have hfactor : 2 * σ last - (∑ i, Y i * σ i) / 2 = 0 :=
    (mul_eq_zero.mp hzero).resolve_left hY
  linarith

end
end PhosphorylationStableCapacity
