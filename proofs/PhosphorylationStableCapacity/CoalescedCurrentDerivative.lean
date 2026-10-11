module
public import proofs.PhosphorylationStableCapacity.CoalescedBindingDerivative
public import proofs.PhosphorylationStableCapacity.LoadedCurrentDerivative

@[expose] public section

namespace PhosphorylationStableCapacity

open Filter
open PhosphorylationSharpness

noncomputable section

def coalescedCatalyticWeight (m : ℕ) (r : ℝ) (i : Fin (m + 2)) : ℝ :=
  (coalescedFiniteRates (m + 1) r).c i *
    (coalescedFiniteState (m + 1) r).C i

/-- The literal coalesced source has balanced catalytic currents. -/
theorem coalescedCatalyticWeight_eq_reverse
    (m : ℕ) (r : ℝ) (i : Fin (m + 2))
    (hpos : (coalescedFiniteState (m + 1) r).Positive) :
    coalescedCatalyticWeight m r i =
      (coalescedFiniteRates (m + 1) r).gamma i *
        (coalescedFiniteState (m + 1) r).D i := by
  have hB : (coalescedRawB (m + 1) r).coeff i ≠ 0 := by
    intro hzero
    have hCi : (coalescedFiniteState (m + 1) r).C i ≠ 0 :=
      ne_of_gt (hpos.2.2.2.1 i)
    apply hCi
    simp [coalescedFiniteState, reconstruct, hzero]
  have h := realize_reconstruct_catalytic_balance
    (fun j : Fin (m + 3) =>
      ((1 + Polynomial.X) * coalescedRawD (m + 1) r).coeff j)
    (fun j : Fin (m + 2) => (coalescedRawB (m + 1) r).coeff j)
    (fun j : Fin (m + 2) => (coalescedRawD (m + 1) r).coeff j)
    (ratio 3) (rootS 3 ((coalescedRawD (m + 1) r).eval (ratio 3)))
    (rootF 3) i hB
  exact h

/-- The source realization has unit reverse catalytic rates, so its common
edge current is the literal phosphatase complex concentration. -/
theorem coalescedCatalyticWeight_eq_D
    (m : ℕ) (r : ℝ) (i : Fin (m + 2))
    (hpos : (coalescedFiniteState (m + 1) r).Positive) :
    coalescedCatalyticWeight m r i =
      (coalescedFiniteState (m + 1) r).D i := by
  rw [coalescedCatalyticWeight_eq_reverse m r i hpos]
  simp [coalescedFiniteRates, realize]

/-- The catalytic current at each literal source edge has the expected
loaded-feedback derivative along every free-substrate tangent. -/
theorem coalescedCatalyticCurrent_hasDerivAt_bindingPath
    (m : ℕ) (r : ℝ) (σ : Fin (m + 3) → ℝ) (i : Fin (m + 2))
    (hpos : (coalescedFiniteState (m + 1) r).Positive)
    (hC : (∑ j : Fin (m + 2),
      (coalescedFiniteState (m + 1) r).C j) = 2 * r - 1)
    (hD : (∑ j : Fin (m + 2),
      (coalescedFiniteState (m + 1) r).D j) = 1)
    (hr : r ≠ 0) :
    HasDerivAt (fun t : ℝ =>
      bindingCatalyticCurrent (2 * r) 2 (coalescedBindingP m r)
        (coalescedBindingQ m r) Fin.castSucc Fin.succ
        (coalescedFiniteRates (m + 1) r).c
        (coalescedFiniteRates (m + 1) r).gamma
        (bindingLinearPath (coalescedFiniteState (m + 1) r).S σ t) i)
      (coalescedCatalyticWeight m r i *
        (σ i.castSucc - σ i.succ +
          (∑ j, coalescedFiniteYLevel m r j * σ j) / 2 -
          (∑ j, coalescedFiniteCLevel m r j * σ j) / (2 * r))) 0 := by
  have hS : ∀ j : Fin (m + 3),
      (coalescedFiniteState (m + 1) r).S j ≠ 0 :=
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
  have hleft : coalescedFiniteCLevel m r i.castSucc =
      (coalescedFiniteState (m + 1) r).C i := by
    simp [coalescedFiniteCLevel, i.isLt]
  have hright : coalescedFiniteYLevel m r i.succ =
      (coalescedFiniteState (m + 1) r).D i := by
    simp [coalescedFiniteYLevel, Fin.val_succ]
  have h := bindingCatalyticCurrent_hasDerivAt_from_concentrations
    (2 * r) 2 (coalescedFiniteState (m + 1) r).S
    (coalescedFiniteCLevel m r) (coalescedFiniteYLevel m r) σ
    Fin.castSucc Fin.succ
    (coalescedFiniteRates (m + 1) r).c
    (coalescedFiniteRates (m + 1) r).gamma
    (coalescedCatalyticWeight m r) i
    hS hET hFT hET0 (by norm_num)
    (by simp [coalescedCatalyticWeight, hleft])
    (by rw [hright]; exact (coalescedCatalyticWeight_eq_reverse m r i hpos).symm)
  change HasDerivAt (fun t : ℝ =>
    bindingCatalyticCurrent (2 * r) 2
      (fun j => coalescedFiniteCLevel m r j /
        (coalescedFiniteState (m + 1) r).S j)
      (fun j => coalescedFiniteYLevel m r j /
        (coalescedFiniteState (m + 1) r).S j)
      Fin.castSucc Fin.succ
      (coalescedFiniteRates (m + 1) r).c
      (coalescedFiniteRates (m + 1) r).gamma
      (bindingLinearPath (coalescedFiniteState (m + 1) r).S σ t) i)
    (coalescedCatalyticWeight m r i *
      (σ i.castSucc - σ i.succ +
        (∑ j, coalescedFiniteYLevel m r j * σ j) / 2 -
        (∑ j, coalescedFiniteCLevel m r j * σ j) / (2 * r))) 0
  exact h

/-- The current derivative in the literal source weight used by the path
limit: the phosphatase complex at the same edge. -/
theorem coalescedCatalyticCurrent_hasDerivAt_D_weight
    (m : ℕ) (r : ℝ) (σ : Fin (m + 3) → ℝ) (i : Fin (m + 2))
    (hpos : (coalescedFiniteState (m + 1) r).Positive)
    (hC : (∑ j : Fin (m + 2),
      (coalescedFiniteState (m + 1) r).C j) = 2 * r - 1)
    (hD : (∑ j : Fin (m + 2),
      (coalescedFiniteState (m + 1) r).D j) = 1)
    (hr : r ≠ 0) :
    HasDerivAt (fun t : ℝ =>
      bindingCatalyticCurrent (2 * r) 2 (coalescedBindingP m r)
        (coalescedBindingQ m r) Fin.castSucc Fin.succ
        (coalescedFiniteRates (m + 1) r).c
        (coalescedFiniteRates (m + 1) r).gamma
        (bindingLinearPath (coalescedFiniteState (m + 1) r).S σ t) i)
      ((coalescedFiniteState (m + 1) r).D i *
        (σ i.castSucc - σ i.succ +
          (∑ j, coalescedFiniteYLevel m r j * σ j) / 2 -
          (∑ j, coalescedFiniteCLevel m r j * σ j) / (2 * r))) 0 := by
  simpa only [coalescedCatalyticWeight_eq_D m r i hpos] using
    coalescedCatalyticCurrent_hasDerivAt_bindingPath m r σ i hpos hC hD hr

/-- The literal source current derivative holds uniformly over every edge and
substrate tangent once the coalesced parameter is sufficiently large. -/
theorem coalescedCatalyticCurrent_eventually_hasDerivAt_bindingPath (m : ℕ) :
    ∀ᶠ r : ℝ in atTop,
      ∀ (σ : Fin (m + 3) → ℝ) (i : Fin (m + 2)),
        HasDerivAt (fun t : ℝ =>
          bindingCatalyticCurrent (2 * r) 2 (coalescedBindingP m r)
            (coalescedBindingQ m r) Fin.castSucc Fin.succ
            (coalescedFiniteRates (m + 1) r).c
            (coalescedFiniteRates (m + 1) r).gamma
            (bindingLinearPath (coalescedFiniteState (m + 1) r).S σ t) i)
          ((coalescedFiniteState (m + 1) r).D i *
            (σ i.castSucc - σ i.succ +
              (∑ j, coalescedFiniteYLevel m r j * σ j) / 2 -
              (∑ j, coalescedFiniteCLevel m r j * σ j) / (2 * r))) 0 := by
  filter_upwards [coalescedFiniteState_eventually_equilibrium (m + 1),
    coalescedFiniteState_eventually_component_totals (m + 1),
    eventually_gt_atTop (0 : ℝ)] with r hstate htot hr
  intro σ i
  exact coalescedCatalyticCurrent_hasDerivAt_D_weight m r σ i
    hstate.2.1 htot.1 htot.2.1 (ne_of_gt hr)

end
end PhosphorylationStableCapacity
