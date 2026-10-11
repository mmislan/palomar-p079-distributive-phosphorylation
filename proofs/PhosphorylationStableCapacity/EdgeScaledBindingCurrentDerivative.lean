module
public import proofs.PhosphorylationStableCapacity.EdgeScaledLoadedField
public import proofs.PhosphorylationStableCapacity.CoalescedInverseCurrentDerivative

@[expose] public section

namespace PhosphorylationStableCapacity

open Filter PhosphorylationSharpness

noncomputable section

theorem edgeScaled_bindingCatalyticCurrent {ι ε : Type*}
    [Fintype ι] (ET FT : ℝ) (p q : ι → ℝ)
    (left right : ε → ι) (w : ε → ℝ)
    (kc ky : ε → ℝ) (S : ι → ℝ) (i : ε) :
    bindingCatalyticCurrent ET FT p q left right
      (fun j => w j * kc j) (fun j => w j * ky j) S i =
        w i * bindingCatalyticCurrent ET FT p q left right kc ky S i := by
  simp only [bindingCatalyticCurrent]
  ring

/-- Literal per-edge rate scaling multiplies each coalesced binding-current
path derivative by its edge weight. -/
theorem coalescedEdgeScaledCurrent_eventually_hasDerivAt (m : ℕ) :
    ∀ᶠ r : ℝ in atTop,
      ∀ (τ : ℝ) (q : Fin (m + 3) → ℝ) (i : Fin (m + 2)),
        HasDerivAt (fun t : ℝ =>
          bindingCatalyticCurrent (2 * r) 2
            (coalescedBindingP m r) (coalescedBindingQ m r)
            Fin.castSucc Fin.succ
            (coalescedFinalScaledRates m r τ).c
            (coalescedFinalScaledRates m r τ).gamma
            (bindingLinearPath (coalescedFiniteState (m + 1) r).S
              (coalescedInverseResponse m r q) t) i)
          (coalescedFinalCurrentWeights m τ i *
            (coalescedCurrentJacobianMatrix m r).mulVec
              (coalescedInverseResponse m r q) i) 0 := by
  filter_upwards [coalescedInverseCurrent_eventually_hasDerivAt m]
    with r hcurrent
  intro τ q i
  have h := (hcurrent q i).const_mul
    (coalescedFinalCurrentWeights m τ i)
  simpa only [coalescedFinalScaledRates, edgeScaledRates,
    edgeScaled_bindingCatalyticCurrent] using h

end
end PhosphorylationStableCapacity
