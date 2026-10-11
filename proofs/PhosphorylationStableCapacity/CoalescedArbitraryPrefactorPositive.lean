module
public import proofs.PhosphorylationStableCapacity.CoalescedArbitraryPrefactor

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section

open PhosphorylationSharpness Polynomial

/-- The common coalesced source state has a nonvanishing denominator in
    the physical prefactor, uniformly in the offset index. -/
theorem arbitrarySplitFiniteState_zero_mass_den_ne_zero
    (m : ℕ) (ξ : ℕ → ℝ) (r : ℝ)
    (hD₀ : DensePositive (coalescedRawD (m+1) r) (m+1))
    (hB₀ : DensePositive (coalescedRawB (m+1) r) (m+1))
    (j : Fin (2*(m+1)+1)) :
    (arbitrarySplitFiniteState (m+1) ξ r 0 j).S 0 *
      (arbitrarySplitFiniteState (m+1) ξ r 0 j).E *
      (arbitrarySplitFiniteState (m+1) ξ r 0 j).F ≠ 0 := by
  have hD : DensePositive (arbitrarySplitRawD (m+1) ξ r 0) (m+1) := by
    simpa [arbitrarySplitRawD, coalescedRawD,
      arbitrarySplitPair_zero_eq_coalesced] using hD₀
  have hB : DensePositive (arbitrarySplitRawB (m+1) ξ r 0) (m+1) := by
    simpa [arbitrarySplitRawB, coalescedRawB,
      arbitrarySplitPair_zero_eq_coalesced] using hB₀
  have hy : 1 < offsetSplitRoot ξ 0 j.val := by
    norm_num [offsetSplitRoot]
  have hx := (arbitrarySplitFiniteState_source_of_conversion_positive
    (m+1) ξ r 0 hD hB j hy).2.1
  exact mul_ne_zero (mul_ne_zero (ne_of_gt (hx.1 0))
    (ne_of_gt hx.2.1)) (ne_of_gt hx.2.2.1)

/-- The common printed physical numerator is positive. This is the sign
    needed before dividing by the positive transverse characteristic factor. -/
theorem arbitrarySplitPhysicalPrefactor_zero_pos
    (m : ℕ) (ξ : ℕ → ℝ) (r τ ε : ℝ)
    (hr : 1 < r) (hτ : 0 < τ) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hD₀ : DensePositive (coalescedRawD (m+1) r) (m+1))
    (hB₀ : DensePositive (coalescedRawB (m+1) r) (m+1))
    (j : Fin (2*(m+1)+1)) :
    0 < arbitrarySplitPhysicalPrefactor m ξ r τ ε j 0 := by
  let k := relaxRates (coalescedFinalScaledRates m r τ) ε
  let x := coalescedFiniteState (m+1) r
  let C := 2*r*(coalescedPair (m+1)).1.eval r+
    (coalescedPair (m+1)).2.eval r
  let M := kinaseComplexInventory k 1-phosphataseComplexInventory k 1
  let R := ∏ i : Fin (m+2),
    (k.b i+k.c i)*k.alpha i*k.gamma i
  have hD : DensePositive (arbitrarySplitRawD (m+1) ξ r 0) (m+1) := by
    simpa [arbitrarySplitRawD, coalescedRawD,
      arbitrarySplitPair_zero_eq_coalesced] using hD₀
  have hB : DensePositive (arbitrarySplitRawB (m+1) ξ r 0) (m+1) := by
    simpa [arbitrarySplitRawB, coalescedRawB,
      arbitrarySplitPair_zero_eq_coalesced] using hB₀
  have hy : 1 < offsetSplitRoot ξ 0 j.val := by
    norm_num [offsetSplitRoot]
  obtain ⟨hk, hx, heq, hET, hFT, _⟩ :=
    arbitrarySplitRetunedState_source_of_conversion_positive
      m ξ r τ 0 ε hτ hε hε1 hD hB j hy
  rw [arbitrarySplitRetunedRates_zero_eq_coalesced] at hk heq
  rw [arbitrarySplitFiniteState_zero_eq_coalesced] at hx heq hET hFT
  have hEF := coalescedFiniteState_EF (m+1) r
  have hM : 0 < M := by
    have h := equilibrium_unit_enzymes_inventory_difference
      k x r hk hx heq hEF.1 hEF.2 hET hFT
    have hs : 0 < x.S 0 := hx.1 0
    have hp : 0 < x.S 0 * M := by rw [h]; linarith
    exact (mul_pos_iff_of_pos_left hs).mp hp
  have hC : 0 < C := by
    have hp := (coalescedPair_dense (m+1)).1.eval_pos (by linarith : 0 < r)
    have hq := (coalescedPair_dense (m+1)).2.eval_pos (by linarith : 0 < r)
    dsimp [C]
    positivity
  have hR : 0 < R := by
    dsimp [R]
    apply Finset.prod_pos
    intro i hi
    obtain ⟨_, hb, hc, hα, _, hγ⟩ := hk i
    positivity
  have hd : 0 < (coalescedRawD (m+1) r).eval 1 :=
    hD₀.eval_pos (by norm_num)
  have hden : 0 < (r-1)*(coalescedRawD (m+1) r).eval 1 :=
    mul_pos (by linarith) hd
  rw [arbitrarySplitPhysicalPrefactor_zero_eq_printed
    m ξ r τ ε hr hτ hε hε1 hD₀ hB₀ j]
  change 0 < (4*C*M/((r-1)*(coalescedRawD (m+1) r).eval 1))*R
  positivity

end
end PhosphorylationStableCapacity
