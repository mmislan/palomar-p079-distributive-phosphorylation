module
public import proofs.PhosphorylationStableCapacity.PaperFixedBindingRealization435
public import proofs.PhosphorylationStableCapacity.CoalescedAllCurrentRateContinuity435

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section

open PhosphorylationSharpness

/-- The manuscript's fixed-binding freedom is a continuous rational map
on the positive-rate domain. -/
theorem continuous_paperFixedBinding_rateVector
    {α : Type*} [TopologicalSpace α] {n : ℕ}
    (k : α → Rates n)
    (hk : Continuous (fun t => rateVector (k t)))
    (hpos : ∀ t, (k t).Positive) :
    Continuous (fun t => rateVector (paperFixedBindingRates (k t))) := by
  apply continuous_pi
  intro j
  apply continuous_pi
  intro i
  have hcoord (q : Fin 6) :
      Continuous (fun t => rateVector (k t) q i) :=
    (continuous_apply i : Continuous (fun v : Fin n → ℝ => v i)).comp
      ((continuous_apply q : Continuous (fun v : Fin 6 → Fin n → ℝ => v q)).comp hk)
  have ha : Continuous (fun t => (k t).a i) := by
    simpa [rateVector] using hcoord 0
  have hb : Continuous (fun t => (k t).b i) := by
    simpa [rateVector] using hcoord 1
  have hc : Continuous (fun t => (k t).c i) := by
    simpa [rateVector] using hcoord 2
  have halpha : Continuous (fun t => (k t).alpha i) := by
    simpa [rateVector] using hcoord 3
  have hbeta : Continuous (fun t => (k t).beta i) := by
    simpa [rateVector] using hcoord 4
  have hgamma : Continuous (fun t => (k t).gamma i) := by
    simpa [rateVector] using hcoord 5
  have hbc (t : α) : (k t).b i + (k t).c i ≠ 0 :=
    ne_of_gt (add_pos (hpos t i).2.1 (hpos t i).2.2.1)
  have hbg (t : α) : (k t).beta i + (k t).gamma i ≠ 0 :=
    ne_of_gt (add_pos (hpos t i).2.2.2.2.1
      (hpos t i).2.2.2.2.2)
  fin_cases j
  · simpa [rateVector, paperFixedBindingRates,
      sourceBindingP_castSucc] using
      (continuous_const.fun_add hc).fun_mul
        (ha.div₀ (hb.fun_add hc) hbc)
  · simpa [rateVector, paperFixedBindingRates] using
      (continuous_const : Continuous (fun _ : α => (1 : ℝ)))
  · simpa [rateVector, paperFixedBindingRates] using hc
  · simpa [rateVector, paperFixedBindingRates,
      sourceBindingQ_succ] using
      (continuous_const.fun_add hgamma).fun_mul
        (halpha.div₀ (hbeta.fun_add hgamma) hbg)
  · simpa [rateVector, paperFixedBindingRates] using
      (continuous_const : Continuous (fun _ : α => (1 : ℝ)))
  · simpa [rateVector, paperFixedBindingRates] using hgamma

/-- The exact paper family over all positive prefix currents is
continuous in the rate arrays at each coalesced source scale. -/
theorem continuous_coalescedPaperFixedBinding_rateVector
    (m : ℕ) (r τ : ℝ) (hτ : 0 < τ)
    (hbase : (coalescedFiniteRates (m+1) r).Positive) :
    Continuous (fun ω : PositivePrefixCurrents m =>
      rateVector (paperFixedBindingRates
        (coalescedAllScaledRates m r (Fin.lastCases τ ω.val)))) := by
  apply continuous_paperFixedBinding_rateVector
  · exact continuous_coalescedAllCurrent_rateVector_light m r τ
  · intro ω
    apply edgeScaledRates_positive
    · intro i
      cases i using Fin.lastCases with
      | last => simpa using hτ
      | cast i => simpa using ω.property i
    · exact hbase

end

end PhosphorylationStableCapacity
