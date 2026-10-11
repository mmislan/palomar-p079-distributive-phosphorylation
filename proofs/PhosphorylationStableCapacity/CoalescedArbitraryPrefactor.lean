module
public import proofs.PhosphorylationStableCapacity.ArbitrarySplitPhysicalChart
public import proofs.PhosphorylationStableCapacity.CoalescedPhysicalPrefactor

@[expose] public section
set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

namespace PhosphorylationStableCapacity

noncomputable section

open PhosphorylationSharpness Polynomial

private theorem printed_prefactor_scalar_algebra
    (r d s M C R : ℝ) (hr : 1 < r) (hd : d ≠ 0) (hs : s ≠ 0)
    (hM : s*M = 2*(r-1)) :
    ((2*r)*2*R/(s*1*1)) *
      ((1/(2*r)-1/2)*(-3/(2*(r-1)*d))*(2*C)/((3/4)/1)) =
      (4*C*M/((r-1)*d))*R := by
  have hr0 : r ≠ 0 := by linarith
  have hr1 : r-1 ≠ 0 := by linarith
  have hMval : M = 2*(r-1)/s := by
    apply (eq_div_iff hs).2
    nlinarith [hM]
  rw [hMval]
  field_simp [hr0, hr1, hd, hs]
  ring

/-- The common physical coefficient at the coalesced point is exactly the
    manuscript's printed numerator before division by `|Θ₀|`. -/
theorem arbitrarySplitPhysicalPrefactor_zero_eq_printed
    (m : ℕ) (ξ : ℕ → ℝ) (r τ ε : ℝ)
    (hr : 1 < r) (hτ : 0 < τ) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hD₀ : DensePositive (coalescedRawD (m+1) r) (m+1))
    (hB₀ : DensePositive (coalescedRawB (m+1) r) (m+1))
    (j : Fin (2*(m+1)+1)) :
    let k := relaxRates (coalescedFinalScaledRates m r τ) ε
    let M := kinaseComplexInventory k 1-phosphataseComplexInventory k 1
    let C := 2*r*(coalescedPair (m+1)).1.eval r+
      (coalescedPair (m+1)).2.eval r
    arbitrarySplitPhysicalPrefactor m ξ r τ ε j 0 =
      (4*C*M/((r-1)*(coalescedRawD (m+1) r).eval 1)) *
        (∏ i : Fin (m+2),
          (k.b i+k.c i)*k.alpha i*k.gamma i) := by
  dsimp only
  let k := relaxRates (coalescedFinalScaledRates m r τ) ε
  let x := coalescedFiniteState (m+1) r
  let d := (coalescedRawD (m+1) r).eval 1
  let C := 2*r*(coalescedPair (m+1)).1.eval r+
    (coalescedPair (m+1)).2.eval r
  let M := kinaseComplexInventory k 1-phosphataseComplexInventory k 1
  let R := ∏ i : Fin (m+2), (k.b i+k.c i)*k.alpha i*k.gamma i
  have hD : DensePositive (arbitrarySplitRawD (m+1) ξ r 0) (m+1) := by
    simpa [arbitrarySplitRawD, coalescedRawD,
      arbitrarySplitPair_zero_eq_coalesced] using hD₀
  have hB : DensePositive (arbitrarySplitRawB (m+1) ξ r 0) (m+1) := by
    simpa [arbitrarySplitRawB, coalescedRawB,
      arbitrarySplitPair_zero_eq_coalesced] using hB₀
  have hy : 1 < offsetSplitRoot ξ 0 j.val := by
    norm_num [offsetSplitRoot]
  have hsrc := arbitrarySplitRetunedState_source_of_conversion_positive
    m ξ r τ 0 ε hτ hε hε1 hD hB j hy
  obtain ⟨hk, hx, heq, hET, hFT, _⟩ := hsrc
  rw [arbitrarySplitRetunedRates_zero_eq_coalesced] at hk heq
  rw [arbitrarySplitFiniteState_zero_eq_coalesced] at hx heq hET hFT
  have hEF := coalescedFiniteState_EF (m+1) r
  have hE : x.E = 1 := hEF.1
  have hF : x.F = 1 := hEF.2
  have hS : x.S 0 ≠ 0 := ne_of_gt (hx.1 0)
  have hd : d ≠ 0 := ne_of_gt (hD₀.eval_pos (by norm_num))
  have hM : x.S 0*M = 2*(r-1) :=
    equilibrium_unit_enzymes_inventory_difference k x r hk hx heq
      hE hF hET hFT
  have hrawD : (arbitrarySplitRawD (m+1) ξ r 0).eval 1 = d := by
    simp [d, arbitrarySplitRawD, coalescedRawD,
      arbitrarySplitPair_zero_eq_coalesced]
  have hell :
      (arbitrarySplitRawB (m+1) ξ r 0).eval
          (ratio (offsetSplitRoot ξ 0 j.val)) /
        (arbitrarySplitRawD (m+1) ξ r 0).eval
          (ratio (offsetSplitRoot ξ 0 j.val)) - r = r-1 := by
    have hden : (arbitrarySplitRawD (m+1) ξ r 0).eval
        (ratio (offsetSplitRoot ξ 0 j.val)) ≠ 0 := by
      have hu0 : ratio (offsetSplitRoot ξ 0 j.val) = 1 := by
        norm_num [offsetSplitRoot, ratio]
      rw [hu0, hrawD]
      exact hd
    have h := arbitrarySplitChartEll_eq_at_root
      (m+1) ξ r 0 j hy hden
    convert h using 1
    norm_num [offsetSplitRoot, ratio]
  have hchart : chartConversionMultiplier 3 (r-1) (r-1) d =
      -3/(2*(r-1)*d) := by
    have hr1 : r-1 ≠ 0 := by linarith
    norm_num [chartConversionMultiplier, ratio]
    field_simp [hr1, hd]
    ring
  have hconv :
      4*r*(arbitrarySplitPair (m+1) ξ 0).1.eval r+
        (offsetSplitRoot ξ 0 j.val-1)*
          (arbitrarySplitPair (m+1) ξ 0).2.eval r = 2*C := by
    rw [arbitrarySplitConversionPrefactor_zero]
    dsimp [C]
    ring
  have hvalue : arbitrarySplitPhysicalPrefactor m ξ r τ ε j 0 =
      ((2*r)*2*R/(x.S 0*1*1)) *
        ((1/(2*r)-1/2)*(-3/(2*(r-1)*d))*(2*C)/((3/4)/1)) := by
    dsimp only [arbitrarySplitPhysicalPrefactor]
    simp only [arbitrarySplitFiniteState_zero_eq_coalesced,
      arbitrarySplitRetunedRates_zero_eq_coalesced]
    rw [hE, hF]
    simp only [one_pow]
    rw [hell, hconv]
    norm_num [offsetSplitRoot, ratio] at hchart ⊢
    rw [hrawD]
    rw [hchart]
  rw [hvalue]
  exact printed_prefactor_scalar_algebra r d (x.S 0) M C R
    hr hd hS hM

end
end PhosphorylationStableCapacity
