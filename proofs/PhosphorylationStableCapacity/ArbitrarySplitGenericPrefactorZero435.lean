module
public import proofs.PhosphorylationStableCapacity.ArbitrarySplitGenericPhysical435
public import proofs.PhosphorylationStableCapacity.CoalescedPhysicalPrefactor
public import proofs.PhosphorylationStableCapacity.CoalescedArbitraryPrefactor

@[expose] public section
set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

namespace PhosphorylationStableCapacity

noncomputable section

open PhosphorylationSharpness Polynomial

private theorem generic_printed_prefactor_scalar_algebra
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

/-- At coalescence the exact physical numerator is independent of the
split-root index and has the manuscript's printed geometric coefficient
times the chosen literal rate product. -/
theorem arbitrarySplitGenericPhysicalPrefactor_zero_eq_printed
    (m : ℕ) (ξ : ℕ → ℝ) (r : ℝ)
    (k : Rates (m+2)) (j : Fin (2*(m+1)+1))
    (hr : 1 < r)
    (hD₀ : DensePositive (coalescedRawD (m+1) r) (m+1))
    (hk : k.Positive)
    (hx : (coalescedFiniteState (m+1) r).Positive)
    (heq : Equilibrium k (coalescedFiniteState (m+1) r))
    (hET : totalE (coalescedFiniteState (m+1) r) = 2*r)
    (hFT : totalF (coalescedFiniteState (m+1) r) = 2) :
    let M := kinaseComplexInventory k 1-phosphataseComplexInventory k 1
    let C := 2*r*(coalescedPair (m+1)).1.eval r+
      (coalescedPair (m+1)).2.eval r
    arbitrarySplitGenericPhysicalPrefactor m ξ r 0 k j =
      (4*C*M/((r-1)*(coalescedRawD (m+1) r).eval 1)) *
        (∏ i : Fin (m+2),
          (k.b i+k.c i)*k.alpha i*k.gamma i) := by
  dsimp only
  let x := coalescedFiniteState (m+1) r
  let d := (coalescedRawD (m+1) r).eval 1
  let C := 2*r*(coalescedPair (m+1)).1.eval r+
    (coalescedPair (m+1)).2.eval r
  let M := kinaseComplexInventory k 1-phosphataseComplexInventory k 1
  let R := ∏ i : Fin (m+2), (k.b i+k.c i)*k.alpha i*k.gamma i
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
  have hy : 1 < offsetSplitRoot ξ 0 j.val := by
    norm_num [offsetSplitRoot]
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
  have hvalue : arbitrarySplitGenericPhysicalPrefactor m ξ r 0 k j =
      ((2*r)*2*R/(x.S 0*1*1)) *
        ((1/(2*r)-1/2)*(-3/(2*(r-1)*d))*(2*C)/((3/4)/1)) := by
    dsimp only [arbitrarySplitGenericPhysicalPrefactor]
    simp only [arbitrarySplitFiniteState_zero_eq_coalesced]
    rw [hE, hF]
    simp only [one_pow]
    rw [hell, hconv]
    norm_num [offsetSplitRoot, ratio] at hchart ⊢
    rw [hrawD]
    rw [hchart]
  rw [hvalue]
  exact generic_printed_prefactor_scalar_algebra r d (x.S 0) M C R
    hr hd hS hM

theorem arbitrarySplitGenericPhysicalPrefactor_zero_pos
    (m : ℕ) (ξ : ℕ → ℝ) (r : ℝ)
    (k : Rates (m+2)) (j : Fin (2*(m+1)+1))
    (hr : 1 < r)
    (hD₀ : DensePositive (coalescedRawD (m+1) r) (m+1))
    (hk : k.Positive)
    (hx : (coalescedFiniteState (m+1) r).Positive)
    (heq : Equilibrium k (coalescedFiniteState (m+1) r))
    (hET : totalE (coalescedFiniteState (m+1) r) = 2*r)
    (hFT : totalF (coalescedFiniteState (m+1) r) = 2) :
    0 < arbitrarySplitGenericPhysicalPrefactor m ξ r 0 k j := by
  let x := coalescedFiniteState (m+1) r
  let M := kinaseComplexInventory k 1-phosphataseComplexInventory k 1
  let C := 2*r*(coalescedPair (m+1)).1.eval r+
    (coalescedPair (m+1)).2.eval r
  let R := ∏ i : Fin (m+2),
    (k.b i+k.c i)*k.alpha i*k.gamma i
  have hEF := coalescedFiniteState_EF (m+1) r
  have hM : 0 < M := by
    have h := equilibrium_unit_enzymes_inventory_difference
      k x r hk hx heq hEF.1 hEF.2 hET hFT
    have hs : 0 < x.S 0 := hx.1 0
    have hp : 0 < x.S 0*M := by rw [h]; linarith
    exact (mul_pos_iff_of_pos_left hs).mp hp
  have hC : 0 < C := by
    have hp := (coalescedPair_dense (m+1)).1.eval_pos
      (by linarith : 0 < r)
    have hq := (coalescedPair_dense (m+1)).2.eval_pos
      (by linarith : 0 < r)
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
  rw [arbitrarySplitGenericPhysicalPrefactor_zero_eq_printed
    m ξ r k j hr hD₀ hk hx heq hET hFT]
  change 0 < (4*C*M/((r-1)*(coalescedRawD (m+1) r).eval 1))*R
  positivity

end

end PhosphorylationStableCapacity
