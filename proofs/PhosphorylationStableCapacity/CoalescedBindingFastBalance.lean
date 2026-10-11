module
public import proofs.PhosphorylationStableCapacity.BindingManifoldFastBalance
public import proofs.PhosphorylationStableCapacity.CoalescedBindingStateIdentity
public import proofs.PhosphorylationStableCapacity.LoadedFastBalance

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section
open PhosphorylationSharpness

/-- The coalesced source's reconstructed binding ratios are the ratios of
its literal forward binding rate to its full complex outflow rate. -/
theorem coalescedBinding_ratios_match_rates (m : ℕ) (r : ℝ)
    (hpos : (coalescedFiniteState (m + 1) r).Positive)
    (heq : Equilibrium (coalescedFiniteRates (m + 1) r)
      (coalescedFiniteState (m + 1) r)) :
    (∀ i : Fin (m + 2),
      (coalescedFiniteRates (m + 1) r).a i =
        ((coalescedFiniteRates (m + 1) r).b i +
          (coalescedFiniteRates (m + 1) r).c i) *
            coalescedBindingP m r i.castSucc) ∧
    (∀ i : Fin (m + 2),
      (coalescedFiniteRates (m + 1) r).alpha i =
        ((coalescedFiniteRates (m + 1) r).beta i +
          (coalescedFiniteRates (m + 1) r).gamma i) *
            coalescedBindingQ m r i.succ) := by
  let x := coalescedFiniteState (m + 1) r
  let k := coalescedFiniteRates (m + 1) r
  have hE : x.E = 1 := (coalescedFiniteState_EF (m + 1) r).1
  have hF : x.F = 1 := (coalescedFiniteState_EF (m + 1) r).2
  constructor
  · intro i
    have hs : x.S i.castSucc ≠ 0 := ne_of_gt (hpos.1 _)
    have hb := equilibrium_kinase_binding_balance k x heq i
    rw [hE, mul_one] at hb
    have hc : coalescedFiniteCLevel m r i.castSucc = x.C i := by
      simp [coalescedFiniteCLevel, i.isLt, x]
    have hr : k.a i = (k.b i + k.c i) * (x.C i / x.S i.castSucc) := by
      calc
        k.a i = k.a i * x.S i.castSucc / x.S i.castSucc := by
          field_simp [hs]
        _ = (k.b i + k.c i) * (x.C i / x.S i.castSucc) := by
          rw [hb]
          ring
    simpa only [coalescedBindingP, hc] using hr
  · intro i
    have hs : x.S i.succ ≠ 0 := ne_of_gt (hpos.1 _)
    have hb := equilibrium_phosphatase_binding_balance k x heq i
    rw [hF, mul_one] at hb
    have hd : coalescedFiniteYLevel m r i.succ = x.D i := by
      simp [coalescedFiniteYLevel, Fin.val_succ, x]
    have hr : k.alpha i =
        (k.beta i + k.gamma i) * (x.D i / x.S i.succ) := by
      calc
        k.alpha i = k.alpha i * x.S i.succ / x.S i.succ := by
          field_simp [hs]
        _ = (k.beta i + k.gamma i) * (x.D i / x.S i.succ) := by
          rw [hb]
          ring
    simpa only [coalescedBindingQ, hd] using hr

/-- Every point of this source's reversible binding manifold has zero fast
complex velocity under the one literal coalesced rate list. -/
theorem coalescedBindingState_fast_zero (m : ℕ) (r : ℝ)
    (hpos : (coalescedFiniteState (m + 1) r).Positive)
    (heq : Equilibrium (coalescedFiniteRates (m + 1) r)
      (coalescedFiniteState (m + 1) r))
    (S : Fin (m + 3) → ℝ) (i : Fin (m + 2)) :
    (field (coalescedFiniteRates (m + 1) r)
      (bindingState (2 * r) 2 (coalescedBindingP m r)
        (coalescedBindingQ m r) S)).C i = 0 ∧
    (field (coalescedFiniteRates (m + 1) r)
      (bindingState (2 * r) 2 (coalescedBindingP m r)
        (coalescedBindingQ m r) S)).D i = 0 := by
  obtain ⟨hp, hq⟩ := coalescedBinding_ratios_match_rates m r hpos heq
  exact bindingState_fast_balance (2 * r) 2
    (coalescedBindingP m r) (coalescedBindingQ m r)
    (coalescedFiniteRates (m + 1) r) hp hq S i

end
end PhosphorylationStableCapacity
