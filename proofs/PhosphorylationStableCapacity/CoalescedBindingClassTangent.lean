module
public import proofs.PhosphorylationStableCapacity.CoalescedArbitraryInventoryDerivative
public import proofs.PhosphorylationStableCapacity.CoalescedBindingStateIdentity
public import proofs.PhosphorylationStableCapacity.BindingStateEnzymeTangent

@[expose] public section

namespace PhosphorylationStableCapacity

open Filter PhosphorylationSharpness

noncomputable section

/-- At every sufficiently large source parameter the two binding
denominators at the literal coalesced state are nonzero. -/
theorem coalescedBindingDenominators_eventually_ne_zero (m : ℕ) :
    ∀ᶠ r : ℝ in atTop,
      bindingDenominator (coalescedBindingP m r)
          (coalescedFiniteState (m + 1) r).S ≠ 0 ∧
        bindingDenominator (coalescedBindingQ m r)
          (coalescedFiniteState (m + 1) r).S ≠ 0 := by
  filter_upwards [coalescedBindingState_eventually_eq_finiteState m]
    with r hstate
  have hE := congrArg (fun x : State (m + 2) => x.E) hstate
  have hF := congrArg (fun x : State (m + 2) => x.F) hstate
  have hEF := coalescedFiniteState_EF (m + 1) r
  constructor
  · intro hz
    change (2 * r) /
      bindingDenominator (coalescedBindingP m r)
        (coalescedFiniteState (m + 1) r).S =
          (coalescedFiniteState (m + 1) r).E at hE
    rw [hEF.1, hz, div_zero] at hE
    norm_num at hE
  · intro hz
    change (2 : ℝ) /
      bindingDenominator (coalescedBindingQ m r)
        (coalescedFiniteState (m + 1) r).S =
          (coalescedFiniteState (m + 1) r).F at hF
    rw [hEF.2, hz, div_zero] at hF
    norm_num at hF

/-- Every inverse-response binding path is tangent to both fixed enzyme
totals, uniformly over the forcing vector. -/
theorem coalescedBindingPath_enzymeTotals_eventually_hasDerivAt_zero
    (m : ℕ) :
    ∀ᶠ r : ℝ in atTop,
      ∀ q : Fin (m + 3) → ℝ,
        HasDerivAt (fun t : ℝ =>
          totalE (bindingState (2 * r) 2
            (coalescedBindingP m r) (coalescedBindingQ m r)
            (bindingLinearPath (coalescedFiniteState (m + 1) r).S
              (coalescedInverseResponse m r q) t))) 0 0 ∧
        HasDerivAt (fun t : ℝ =>
          totalF (bindingState (2 * r) 2
            (coalescedBindingP m r) (coalescedBindingQ m r)
            (bindingLinearPath (coalescedFiniteState (m + 1) r).S
              (coalescedInverseResponse m r q) t))) 0 0 := by
  filter_upwards [coalescedBindingDenominators_eventually_ne_zero m]
    with r hden
  intro q
  have hp : ∀ T : Fin (m + 3) → ℝ,
      bindingComplex (2 * r) (coalescedBindingP m r) T
        (Fin.last (m + 2)) = 0 :=
    fun T => (coalescedBinding_endpoint_complexes_zero m r T).1
  have hq : ∀ T : Fin (m + 3) → ℝ,
      bindingComplex 2 (coalescedBindingQ m r) T 0 = 0 :=
    fun T => (coalescedBinding_endpoint_complexes_zero m r T).2
  exact ⟨bindingState_totalE_path_hasDerivAt_zero
      (2 * r) 2 (coalescedBindingP m r) (coalescedBindingQ m r)
      (coalescedFiniteState (m + 1) r).S
      (coalescedInverseResponse m r q) hp hden.1,
    bindingState_totalF_path_hasDerivAt_zero
      (2 * r) 2 (coalescedBindingP m r) (coalescedBindingQ m r)
      (coalescedFiniteState (m + 1) r).S
      (coalescedInverseResponse m r q) hq hden.2⟩

/-- Every zero-sum loaded forcing follows a first-order tangent to all
three literal compatibility-class totals. -/
theorem coalescedBindingPath_allTotals_eventually_hasDerivAt_zero
    (m : ℕ) :
    ∀ᶠ r : ℝ in atTop,
      ∀ q : Fin (m + 3) → ℝ,
        (∑ k, q k) = 0 →
        HasDerivAt (fun t : ℝ =>
          totalE (bindingState (2 * r) 2
            (coalescedBindingP m r) (coalescedBindingQ m r)
            (bindingLinearPath (coalescedFiniteState (m + 1) r).S
              (coalescedInverseResponse m r q) t))) 0 0 ∧
        HasDerivAt (fun t : ℝ =>
          totalF (bindingState (2 * r) 2
            (coalescedBindingP m r) (coalescedBindingQ m r)
            (bindingLinearPath (coalescedFiniteState (m + 1) r).S
              (coalescedInverseResponse m r q) t))) 0 0 ∧
        HasDerivAt (fun t : ℝ =>
          totalS (bindingState (2 * r) 2
            (coalescedBindingP m r) (coalescedBindingQ m r)
            (bindingLinearPath (coalescedFiniteState (m + 1) r).S
              (coalescedInverseResponse m r q) t))) 0 0 := by
  filter_upwards [coalescedBindingPath_enzymeTotals_eventually_hasDerivAt_zero m,
    coalescedBindingPath_totalS_eventually_hasDerivAt_zero m]
    with r henz hsub
  intro q hq
  exact ⟨(henz q).1, (henz q).2, hsub q hq⟩

end
end PhosphorylationStableCapacity
