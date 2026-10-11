module
public import proofs.PhosphorylationStableCapacity.PaperFixedBindingJacobianAnalytic

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section

open PhosphorylationSharpness Polynomial

/-- The analytic family uses exactly the common coalesced state and the
fixed-binding rate vector selected by the slow-link argument at δ=0. -/
theorem paperFixedBinding_physical_data_coalesces
    (m : ℕ) (ξ : ℕ → ℝ) (r τ ε : ℝ)
    (ω : Fin (m+1) → ℝ) :
    (∀ j : Fin (2*(m+1)+1),
      arbitrarySplitFiniteState (m+1) ξ r 0 j =
        coalescedFiniteState (m+1) r) ∧
    paperFixedBindingSplitRates m ξ r 0 ε (Fin.lastCases τ ω) =
      relaxRates (paperFixedBindingRates
        (coalescedAllScaledRates m r (Fin.lastCases τ ω))) ε := by
  constructor
  · intro j
    exact arbitrarySplitFiniteState_zero_eq_coalesced (m+1) ξ r j
  · simp [paperFixedBindingSplitRates, coalescedAllScaledRates,
      arbitrarySplitFiniteRates_zero_eq_coalesced]

/-- The paper's frozen-binding rate vector and every labelled physical
species coordinate are analytic in the split distance at coalescence.
This is the literal analytic-data clause preceding the eigenvalue law. -/
theorem paperFixedBinding_all_physical_data_analyticAt
    (m : ℕ) (ξ : ℕ → ℝ) (r τ ε : ℝ)
    (ω : Fin (m+1) → ℝ) (hr : r ≠ 0)
    (hD₀ : DensePositive (coalescedRawD (m+1) r) (m+1))
    (hB₀ : DensePositive (coalescedRawB (m+1) r) (m+1))
    (hbase : (coalescedAllScaledRates m r
      (Fin.lastCases τ ω)).Positive) :
    AnalyticAt ℝ (fun δ => rateVector
      (paperFixedBindingSplitRates m ξ r δ ε
        (Fin.lastCases τ ω))) 0 ∧
    ∀ j : Fin (2*(m+1)+1),
      (∀ i : Fin (m+3), AnalyticAt ℝ
        (fun δ => (arbitrarySplitFiniteState (m+1) ξ r δ j).S i) 0) ∧
      AnalyticAt ℝ
        (fun δ => (arbitrarySplitFiniteState (m+1) ξ r δ j).E) 0 ∧
      AnalyticAt ℝ
        (fun δ => (arbitrarySplitFiniteState (m+1) ξ r δ j).F) 0 ∧
      (∀ i : Fin (m+2), AnalyticAt ℝ
        (fun δ => (arbitrarySplitFiniteState (m+1) ξ r δ j).C i) 0) ∧
      (∀ i : Fin (m+2), AnalyticAt ℝ
        (fun δ => (arbitrarySplitFiniteState (m+1) ξ r δ j).D i) 0) := by
  refine ⟨paperFixedBindingSplit_rateVector_analyticAt
      m ξ r τ ε ω hr hD₀ hB₀ hbase, ?_⟩
  intro j
  exact arbitrarySplitFiniteState_components_analyticAt
    (m+1) ξ r hr hD₀ j

end
end PhosphorylationStableCapacity
