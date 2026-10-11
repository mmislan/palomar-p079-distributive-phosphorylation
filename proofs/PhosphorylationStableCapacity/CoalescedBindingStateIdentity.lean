module
public import proofs.PhosphorylationStableCapacity.CoalescedBindingLevelBridge

@[expose] public section

namespace PhosphorylationStableCapacity

open Filter PhosphorylationSharpness

noncomputable section

/-- At a positive coalesced source state with its stated enzyme totals,
the fixed-total reversible binding realization is that very literal state. -/
theorem coalescedBindingState_eq_finiteState (m : ℕ) (r : ℝ)
    (hpos : (coalescedFiniteState (m + 1) r).Positive)
    (hC : (∑ i : Fin (m + 2),
      (coalescedFiniteState (m + 1) r).C i) = 2 * r - 1)
    (hD : (∑ i : Fin (m + 2),
      (coalescedFiniteState (m + 1) r).D i) = 1)
    (hr : r ≠ 0) :
    bindingState (2 * r) 2 (coalescedBindingP m r)
      (coalescedBindingQ m r)
      (coalescedFiniteState (m + 1) r).S =
        coalescedFiniteState (m + 1) r := by
  let x := coalescedFiniteState (m + 1) r
  have hS : ∀ j : Fin (m + 3), x.S j ≠ 0 :=
    fun j => ne_of_gt (hpos.1 j)
  have hET : 2 * r = 1 + ∑ j : Fin (m + 3),
      coalescedFiniteCLevel m r j := by
    rw [coalescedFiniteCLevel_sum, hC]
    ring
  have hFT : (2 : ℝ) = 1 + ∑ j : Fin (m + 3),
      coalescedFiniteYLevel m r j := by
    rw [coalescedFiniteYLevel_sum, hD]
    ring
  have hET0 : 2 * r ≠ 0 := mul_ne_zero (by norm_num) hr
  have hdenP : bindingDenominator (coalescedBindingP m r) x.S =
      2 * r := by
    change bindingDenominator
      (fun j => coalescedFiniteCLevel m r j / x.S j) x.S = _
    rw [bindingDenominator_ratio x.S (coalescedFiniteCLevel m r) hS]
    exact hET.symm
  have hdenQ : bindingDenominator (coalescedBindingQ m r) x.S =
      2 := by
    change bindingDenominator
      (fun j => coalescedFiniteYLevel m r j / x.S j) x.S = _
    rw [bindingDenominator_ratio x.S (coalescedFiniteYLevel m r) hS]
    exact hFT.symm
  have hBC : bindingComplex (2 * r) (coalescedBindingP m r) x.S =
      coalescedFiniteCLevel m r := by
    funext j
    change bindingComplex (2 * r)
      (fun j => coalescedFiniteCLevel m r j / x.S j) x.S j = _
    exact
      bindingComplex_ratio (2 * r) x.S (coalescedFiniteCLevel m r)
        hS hET hET0 j
  have hBY : bindingComplex 2 (coalescedBindingQ m r) x.S =
      coalescedFiniteYLevel m r := by
    funext j
    change bindingComplex 2
      (fun j => coalescedFiniteYLevel m r j / x.S j) x.S j = _
    exact
      bindingComplex_ratio 2 x.S (coalescedFiniteYLevel m r)
        hS hFT (by norm_num) j
  have hE : (bindingState (2 * r) 2 (coalescedBindingP m r)
      (coalescedBindingQ m r) x.S).E = x.E := by
    change (2 * r) / bindingDenominator (coalescedBindingP m r)
      x.S = x.E
    rw [hdenP, div_self hET0]
    exact (coalescedFiniteState_EF (m + 1) r).1.symm
  have hF : (bindingState (2 * r) 2 (coalescedBindingP m r)
      (coalescedBindingQ m r) x.S).F = x.F := by
    change (2 : ℝ) / bindingDenominator (coalescedBindingQ m r)
      x.S = x.F
    rw [hdenQ]
    norm_num
    exact (coalescedFiniteState_EF (m + 1) r).2.symm
  have hCompC (i : Fin (m + 2)) :
      (bindingState (2 * r) 2 (coalescedBindingP m r)
        (coalescedBindingQ m r) x.S).C i = x.C i := by
    change bindingComplex (2 * r) (coalescedBindingP m r) x.S
      i.castSucc = x.C i
    rw [hBC]
    simp [coalescedFiniteCLevel, i.isLt, x]
  have hCompD (i : Fin (m + 2)) :
      (bindingState (2 * r) 2 (coalescedBindingP m r)
        (coalescedBindingQ m r) x.S).D i = x.D i := by
    change bindingComplex 2 (coalescedBindingQ m r) x.S
      i.succ = x.D i
    rw [hBY]
    simp [coalescedFiniteYLevel, Fin.val_succ, x]
  change bindingState (2 * r) 2 (coalescedBindingP m r)
    (coalescedBindingQ m r) x.S =
      (⟨x.S, x.E, x.F, x.C, x.D⟩ : State (m + 2))
  unfold bindingState
  rw [State.mk.injEq]
  refine ⟨rfl, hE, hF, ?_, ?_⟩
  · funext i
    exact hCompC i
  · funext i
    exact hCompD i

/-- The state identity holds at every sufficiently large literal source
parameter, with positivity and component totals discharged by the source. -/
theorem coalescedBindingState_eventually_eq_finiteState (m : ℕ) :
    ∀ᶠ r : ℝ in atTop,
      bindingState (2 * r) 2 (coalescedBindingP m r)
        (coalescedBindingQ m r)
        (coalescedFiniteState (m + 1) r).S =
          coalescedFiniteState (m + 1) r := by
  filter_upwards [coalescedFiniteState_eventually_equilibrium (m + 1),
    coalescedFiniteState_eventually_component_totals (m + 1),
    eventually_gt_atTop (0 : ℝ)] with r hs ht hr
  exact coalescedBindingState_eq_finiteState m r
    hs.2.1 ht.1 ht.2.1 (ne_of_gt hr)

end
end PhosphorylationStableCapacity
