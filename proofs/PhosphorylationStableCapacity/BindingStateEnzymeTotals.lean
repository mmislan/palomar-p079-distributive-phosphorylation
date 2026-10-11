module
public import proofs.PhosphorylationStableCapacity.LoadedBindingLevelBridge
public import proofs.PhosphorylationStableCapacity.Compatibility

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section
open PhosphorylationSharpness

/-- When the binding denominator is nonzero, bound complexes and free
enzyme partition the prescribed enzyme total. -/
theorem sum_bindingComplex_add_free {ι : Type*} [Fintype ι]
    (ET : ℝ) (p S : ι → ℝ)
    (hden : bindingDenominator p S ≠ 0) :
    (∑ i, bindingComplex ET p S i) +
      ET / bindingDenominator p S = ET := by
  let d := bindingDenominator p S
  have hsum : (∑ i, bindingComplex ET p S i) =
      ET * (∑ i, p i * S i) / d := by
    calc
      (∑ i, bindingComplex ET p S i) =
          (∑ i, ET * (p i * S i)) / d := by
        rw [Finset.sum_div]
        apply Finset.sum_congr rfl
        intro i _
        unfold bindingComplex
        dsimp [d]
        ring
      _ = ET * (∑ i, p i * S i) / d := by
        rw [Finset.mul_sum]
  rw [hsum]
  have hd : d = 1 + ∑ i, p i * S i := rfl
  rw [show (∑ i, p i * S i) = d - 1 by linear_combination -hd]
  change ET * (d - 1) / d + ET / d = ET
  have hd0 : d ≠ 0 := hden
  field_simp [hd0]
  ring

/-- The reversible binding state has exactly its prescribed kinase total
when its terminal kinase complex is absent. -/
theorem bindingState_totalE {n : ℕ} (ET FT : ℝ)
    (p q S : Fin (n + 1) → ℝ)
    (hp : bindingComplex ET p S (Fin.last n) = 0)
    (hden : bindingDenominator p S ≠ 0) :
    totalE (bindingState ET FT p q S) = ET := by
  have hsum : (∑ i : Fin n,
      bindingComplex ET p S i.castSucc) =
        ∑ j : Fin (n + 1), bindingComplex ET p S j := by
    rw [Fin.sum_univ_castSucc, hp, add_zero]
  change ET / bindingDenominator p S +
      (∑ i : Fin n, bindingComplex ET p S i.castSucc) = ET
  rw [hsum]
  linear_combination sum_bindingComplex_add_free ET p S hden

/-- The analogous exact phosphatase-total identity. -/
theorem bindingState_totalF {n : ℕ} (ET FT : ℝ)
    (p q S : Fin (n + 1) → ℝ)
    (hq : bindingComplex FT q S 0 = 0)
    (hden : bindingDenominator q S ≠ 0) :
    totalF (bindingState ET FT p q S) = FT := by
  have hsum : (∑ i : Fin n,
      bindingComplex FT q S i.succ) =
        ∑ j : Fin (n + 1), bindingComplex FT q S j := by
    rw [Fin.sum_univ_succ, hq, zero_add]
  change FT / bindingDenominator q S +
      (∑ i : Fin n, bindingComplex FT q S i.succ) = FT
  rw [hsum]
  linear_combination sum_bindingComplex_add_free FT q S hden

end
end PhosphorylationStableCapacity
