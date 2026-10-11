module
public import proofs.PhosphorylationStableCapacity.PaperFixedBindingIndependentPoint435
public import proofs.PhosphorylationStableCapacity.PaperFixedBindingRationalAttainment

@[expose] public section

namespace PhosphorylationStableCapacity
noncomputable section
open PhosphorylationSharpness Polynomial Filter
open scoped Topology

theorem paper_fixed_binding_rational_attainment (m : ℕ) :
    PaperFixedBindingRationalAttainment m := by
  obtain ⟨a, b, c, hrAdequate, ht, hprefix, hfinal, hstateZero,
    hrateZero, hrateAnalytic, hstateAnalytic, lam, hlam, α, K,
    hα, hK, hA, hcoefficient, hEv, d, hkRat, hsRat, hfinite,
    _, _⟩ :=
    paperFixedBinding_rational_actual_current_analytic_family_attainment m
  let ξ : ℕ → ℝ := fun j => (j : ℝ)
  let x : Fin (2*(m+1)+1) → ℝ := fun j => (j.val : ℝ)
  let r : ℝ := 2^a; let t : ℝ := (1/2)^b; let ε : ℝ := (1/2)^c
  let s₀ := coalescedFiniteState (m+1) r
  let τ : ℝ := t/s₀.D (Fin.last (m+1))
  let θ : Fin (m+1) → ℝ := fun i => 1/s₀.D i.castSucc
  have hr : 0 < r := lt_of_lt_of_le (by positivity) hrAdequate
  have hrateAnalyticLocal : AnalyticAt ℝ (fun δ => rateVector
      (paperFixedBindingSplitRates m ξ r δ ε (Fin.lastCases τ θ))) 0 := by
    simpa only [ξ, r, t, ε, τ, θ, s₀] using hrateAnalytic
  have hfamily : PaperFixedBindingFamilyData m ξ r t ε
      (Fin.lastCases τ θ) := by
    simp only [PaperFixedBindingFamilyData,
      paperCoalescedState_eq_coalescedFiniteState,
      paperSourceRates_eq_arbitrarySplitFiniteRates,
      paperSourceState_eq_arbitrarySplitFiniteState,
      paperRates_eq_paperFixedBindingSplitRates,
      paperFixBinding_eq_paperFixedBindingRates]
    refine ⟨hrAdequate, ht, (fun i => ⟨rfl, rfl⟩), ?_, ?_,
      hstateZero, ?_, hstateAnalytic⟩
    · rw [hrateZero]
      simpa only [r] using hprefix
    · rw [hrateZero]
      simpa only [r, t] using hfinal
    · intro i
      have hc (q : Fin 6) :=
        (analyticAt_pi_iff.mp (analyticAt_pi_iff.mp hrateAnalyticLocal q)) i
      exact ⟨by simpa [rateVector] using hc 0,
        by simpa [rateVector] using hc 1, by simpa [rateVector] using hc 2,
        by simpa [rateVector] using hc 3, by simpa [rateVector] using hc 4,
        by simpa [rateVector] using hc 5⟩
  have hselected : PaperFixedBindingSelectedLaw m x ξ r ε
      (paperFixedBindingPrintedCoefficient m r τ ε θ) α K
      (Fin.lastCases τ θ) lam := by
    simp only [PaperFixedBindingSelectedLaw,
      paperCoalescedState_eq_coalescedFiniteState,
      paperRates_eq_paperFixedBindingSplitRates,
      paperCoalescedPair_eq_coalescedPair,
      paperCoalescedD_eq_coalescedRawD, paperCoalescedB_eq_coalescedRawB]
    refine ⟨hlam, hA, hα, hK, ?_, ?_⟩
    · rw [hrateZero]
      have hcoord : fromLoadedCoord (loadedCoordOfState
          (coalescedFiniteState (m+1) ((2 : ℝ)^a))) =
          toCoordinateSpace (chart (coalescedFiniteState (m+1) ((2 : ℝ)^a))) := by
        simp [loadedCoordOfState, from_toLoadedCoord]
      simpa only [r, t, ε, τ, θ, s₀, hcoord] using hcoefficient
    · filter_upwards [hEv] with δ hd
      exact paper_fixed_binding_completePoint_to_signedLawAt
        m x ξ (fun j => rfl) r τ ε α K δ θ lam hr hα hd
  have hpoint : PaperFixedBindingSignedLawAt m x ξ r ((1/2 : ℝ)^d) ε
      (paperFixedBindingPrintedCoefficient m r τ ε θ) α K
      (Fin.lastCases τ θ) lam :=
    paper_fixed_binding_completePoint_to_signedLawAt
      m x ξ (fun j => rfl) r τ ε α K ((1/2 : ℝ)^d) θ lam
      hr hα hfinite.1
  refine ⟨a, b, c, ?_, lam,
    paperFixedBindingPrintedCoefficient m r τ ε θ, α, K, ?_, d, ?_, ?_, ?_⟩
  · simpa only [r, t, ε, τ, θ, s₀,
      paperCoalescedState_eq_coalescedFiniteState] using hfamily
  · simpa only [r, t, ε, τ, θ, s₀,
      paperCoalescedState_eq_coalescedFiniteState] using hselected
  · simpa only [paperCoalescedState_eq_coalescedFiniteState,
      paperRates_eq_paperFixedBindingSplitRates] using hkRat
  · intro j
    simpa only [paperCoalescedState_eq_coalescedFiniteState,
      paperSourceState_eq_arbitrarySplitFiniteState] using hsRat j
  · simpa only [r, t, ε, τ, θ, s₀,
      paperCoalescedState_eq_coalescedFiniteState] using hpoint

end
end PhosphorylationStableCapacity
