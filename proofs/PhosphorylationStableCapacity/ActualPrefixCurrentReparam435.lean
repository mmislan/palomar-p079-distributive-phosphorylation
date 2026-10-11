module
public import proofs.PhosphorylationStableCapacity.PositivePrefixCurrents435
public import proofs.PhosphorylationStableCapacity.AllCurrentWeightedDerivative435
public import proofs.PhosphorylationStableCapacity.RelaxationRates
public import proofs.PhosphorylationStableCapacity.PaperFixedBindingRealization435

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section

open PhosphorylationSharpness

/-- Convert the paper's actual coalesced catalytic prefix currents to
the edge-rate factors used by the mass-action retuning construction.
The positive coalesced phosphatase complexes are fixed as the currents
vary. -/
def edgePrefixFactorsOfActualCurrent
    (m : ℕ) (r : ℝ)
    (hstate : (coalescedFiniteState (m+1) r).Positive)
    (ω : PositivePrefixCurrents m) : PositivePrefixCurrents m :=
  ⟨fun i => ω.val i /
      (coalescedFiniteState (m+1) r).D i.castSucc,
    fun i => div_pos (ω.property i)
      (hstate.2.2.2.2 i.castSucc)⟩

theorem continuous_edgePrefixFactorsOfActualCurrent
    (m : ℕ) (r : ℝ)
    (hstate : (coalescedFiniteState (m+1) r).Positive) :
    Continuous (edgePrefixFactorsOfActualCurrent m r hstate) := by
  have hfun : Continuous (fun ω : PositivePrefixCurrents m =>
      fun i : Fin (m+1) => ω.val i /
        (coalescedFiniteState (m+1) r).D i.castSucc) := by
    apply continuous_pi
    intro i
    have hcoord : Continuous
        (fun ω : PositivePrefixCurrents m => ω.val i) :=
      (continuous_apply i).comp continuous_subtype_val
    exact hcoord.div continuous_const
      (fun ω => ne_of_gt (hstate.2.2.2.2 i.castSucc))
  exact hfun.subtype_mk _

/-- A compact set of positive *actual* prefix currents maps to a
compact set of positive edge factors. -/
theorem isCompact_edgePrefixFactorsOfActualCurrent_image
    (m : ℕ) (r : ℝ)
    (hstate : (coalescedFiniteState (m+1) r).Positive)
    (K : Set (PositivePrefixCurrents m)) (hK : IsCompact K) :
    IsCompact ((edgePrefixFactorsOfActualCurrent m r hstate) '' K) :=
  hK.image (continuous_edgePrefixFactorsOfActualCurrent m r hstate)

theorem continuous_fullEdgeFactors_from_positivePrefix
    (m : ℕ) (τ : ℝ) :
    Continuous (fun a : PositivePrefixCurrents m =>
      (Fin.lastCases τ a.val : Fin (m+2) → ℝ)) := by
  apply continuous_pi
  intro i
  cases i using Fin.lastCases with
  | last =>
      simpa only [Fin.lastCases_last] using
        (continuous_const : Continuous
          (fun _ : PositivePrefixCurrents m => τ))
  | cast i =>
      simpa only [Fin.lastCases_castSucc, Function.comp_def] using
        (continuous_apply i).comp continuous_subtype_val

/-- A compact set of actual prefix currents gives a compact family of
full positive edge factors after the manuscript's fixed final current
is adjoined. -/
theorem isCompact_fullEdgeFactors_actual_image
    (m : ℕ) (r τ : ℝ)
    (hstate : (coalescedFiniteState (m+1) r).Positive)
    (K : Set (PositivePrefixCurrents m)) (hK : IsCompact K) :
    IsCompact ((fun ω : PositivePrefixCurrents m =>
      (Fin.lastCases τ
        (edgePrefixFactorsOfActualCurrent m r hstate ω).val : Fin (m+2) → ℝ)) '' K) := by
  exact hK.image
    ((continuous_fullEdgeFactors_from_positivePrefix m τ).comp
      (continuous_edgePrefixFactorsOfActualCurrent m r hstate))

/-- The manuscript's final catalytic current `t` is likewise an
actual flux, so its edge factor is `t/Y_last(0)`. -/
def finalEdgeFactorOfActualCurrent
    (m : ℕ) (r : ℝ)
    (_hstate : (coalescedFiniteState (m+1) r).Positive)
    (t : ℝ) : ℝ :=
  t / (coalescedFiniteState (m+1) r).D (Fin.last (m+1))

theorem finalEdgeFactorOfActualCurrent_pos
    (m : ℕ) (r : ℝ)
    (hstate : (coalescedFiniteState (m+1) r).Positive)
    {t : ℝ} (ht : 0 < t) :
    0 < finalEdgeFactorOfActualCurrent m r hstate t :=
  div_pos ht (hstate.2.2.2.2 (Fin.last (m+1)))

/-- At the common coalesced equilibrium the retuned literal rates
realize exactly the paper's selected positive prefix catalytic current
`ωᵢ=γᵢYᵢ`. -/
theorem coalesced_actual_prefix_current_eq
    (m : ℕ) (r τ ε : ℝ)
    (hstate : (coalescedFiniteState (m+1) r).Positive)
    (ω : PositivePrefixCurrents m) (i : Fin (m+1)) :
    (relaxRates (coalescedAllScaledRates m r
      (Fin.lastCases τ
        (edgePrefixFactorsOfActualCurrent m r hstate ω).val)) ε).gamma
          i.castSucc *
      (coalescedFiniteState (m+1) r).D i.castSucc = ω.val i := by
  have hD : (coalescedFiniteState (m+1) r).D i.castSucc ≠ 0 :=
    ne_of_gt (hstate.2.2.2.2 i.castSucc)
  simp only [relaxRates, coalescedAllScaledRates, edgeScaledRates,
    Fin.lastCases_castSucc]
  change (ω.val i /
      (coalescedFiniteState (m+1) r).D i.castSucc) *
      (coalescedFiniteRates (m+1) r).gamma i.castSucc *
      (coalescedFiniteState (m+1) r).D i.castSucc = ω.val i
  simp [coalescedFiniteRates, realize, hD]

/-- The final edge factor `τ` realizes the actual final catalytic
current `τY_last(0)`, common to every member of the compact prefix set. -/
theorem coalesced_actual_final_current_eq
    (m : ℕ) (r τ ε : ℝ)
    (ω : PositivePrefixCurrents m) :
    (relaxRates (coalescedAllScaledRates m r
      (Fin.lastCases τ ω.val)) ε).gamma (Fin.last (m+1)) *
      (coalescedFiniteState (m+1) r).D (Fin.last (m+1)) =
        τ*(coalescedFiniteState (m+1) r).D (Fin.last (m+1)) := by
  simp [relaxRates, coalescedAllScaledRates, edgeScaledRates,
    coalescedFiniteRates, realize]

theorem coalesced_final_actual_current_reparam_eq
    (m : ℕ) (r t ε : ℝ)
    (hstate : (coalescedFiniteState (m+1) r).Positive)
    (ω : PositivePrefixCurrents m) :
    (relaxRates (coalescedAllScaledRates m r
      (Fin.lastCases (finalEdgeFactorOfActualCurrent m r hstate t)
        (edgePrefixFactorsOfActualCurrent m r hstate ω).val)) ε).gamma
        (Fin.last (m+1)) *
      (coalescedFiniteState (m+1) r).D (Fin.last (m+1)) = t := by
  have hD : (coalescedFiniteState (m+1) r).D (Fin.last (m+1)) ≠ 0 :=
    ne_of_gt (hstate.2.2.2.2 (Fin.last (m+1)))
  rw [coalesced_actual_final_current_eq]
  exact div_mul_cancel₀ t hD

/-- The paper's fixed-binding choice preserves all the actual
catalytic currents because it keeps the two catalytic rate arrays. -/
theorem paperFixedBinding_actual_prefix_current_eq
    (m : ℕ) (r t ε : ℝ)
    (hstate : (coalescedFiniteState (m+1) r).Positive)
    (ω : PositivePrefixCurrents m) (i : Fin (m+1)) :
    (relaxRates (paperFixedBindingRates (coalescedAllScaledRates m r
      (Fin.lastCases (finalEdgeFactorOfActualCurrent m r hstate t)
        (edgePrefixFactorsOfActualCurrent m r hstate ω).val))) ε).gamma
        i.castSucc *
      (coalescedFiniteState (m+1) r).D i.castSucc = ω.val i := by
  simpa only [relaxRates, paperFixedBindingRates] using
    coalesced_actual_prefix_current_eq m r
      (finalEdgeFactorOfActualCurrent m r hstate t) ε hstate ω i

theorem paperFixedBinding_actual_final_current_eq
    (m : ℕ) (r t ε : ℝ)
    (hstate : (coalescedFiniteState (m+1) r).Positive)
    (ω : PositivePrefixCurrents m) :
    (relaxRates (paperFixedBindingRates (coalescedAllScaledRates m r
      (Fin.lastCases (finalEdgeFactorOfActualCurrent m r hstate t)
        (edgePrefixFactorsOfActualCurrent m r hstate ω).val))) ε).gamma
        (Fin.last (m+1)) *
      (coalescedFiniteState (m+1) r).D (Fin.last (m+1)) = t := by
  simpa only [relaxRates, paperFixedBindingRates] using
    coalesced_final_actual_current_reparam_eq m r t ε hstate ω

end

end PhosphorylationStableCapacity
