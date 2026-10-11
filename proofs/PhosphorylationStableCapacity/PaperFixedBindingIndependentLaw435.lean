module
public import proofs.PhosphorylationStableCapacity.PaperFixedBindingIndependentPoint435
public import proofs.PhosphorylationStableCapacity.PaperFixedBindingActualCurrentDesign
public import proofs.PhosphorylationStableCapacity.PaperFixedBindingAnalyticData

@[expose] public section

namespace PhosphorylationStableCapacity
noncomputable section
open PhosphorylationSharpness Polynomial Filter
open scoped Topology

/-- One literal construction supports all offsets and the selected analytic law. -/
theorem paper_fixed_binding_finite_law
    (m : ℕ) (x : Fin (2*(m+1)+1) → ℝ) :
    PaperFixedBindingFiniteLaw m x := by
  intro hx
  obtain ⟨ξ, hξ, hagree⟩ := finite_ordered_offsets_extend (by omega) x hx
  obtain ⟨a, b, c, hr, hrAdequate, ht, hτ, hε, hε1,
    hD, hB, hθ, hbase, hk, hs, heq, hET, hFT,
    hspec, hprefix, hfinal⟩ := paperFixedBinding_actual_unit_current_design m
  let r : ℝ := 2^a
  let t : ℝ := (1/2)^b
  let ε : ℝ := (1/2)^c
  let s₀ := coalescedFiniteState (m+1) r
  let τ : ℝ := t/s₀.D (Fin.last (m+1))
  let θ : Fin (m+1) → ℝ := fun i => 1/s₀.D i.castSucc
  obtain ⟨lam, hlam, hA, α, K, hα, hK, hpoint⟩ :=
    paperFixedBinding_complete_analytic_law m ξ hξ r τ ε θ
      hθ hr hτ hε hε1 hD hB hbase hk hs heq hET hFT hspec
  obtain ⟨hrateAnalytic, hstateAnalytic⟩ :=
    paperFixedBinding_all_physical_data_analyticAt m ξ r τ ε θ
      (ne_of_gt (lt_trans zero_lt_one hr)) hD hB hbase
  obtain ⟨hstateZero, hrateZero⟩ :=
    paperFixedBinding_physical_data_coalesces m ξ r τ ε θ
  have hcoefficient := paperFixedBindingPrintedCoefficient_eq_published_aconst
    m r τ ε θ hr hD hk hs heq hET hFT hspec
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
      exact hprefix
    · rw [hrateZero]
      exact hfinal
    · intro i
      have hc (q : Fin 6) :=
        (analyticAt_pi_iff.mp (analyticAt_pi_iff.mp hrateAnalytic q)) i
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
          (coalescedFiniteState (m+1) r)) =
          toCoordinateSpace (chart (coalescedFiniteState (m+1) r)) := by
        simp [loadedCoordOfState, from_toLoadedCoord]
      simpa only [hcoord] using hcoefficient
    · filter_upwards [hpoint] with δ hd
      exact paper_fixed_binding_completePoint_to_signedLawAt
        m x ξ hagree r τ ε α K δ θ lam (lt_trans zero_lt_one hr) hα hd
  refine ⟨ξ, hξ, hagree, a, b, c, ?_, lam,
    paperFixedBindingPrintedCoefficient m r τ ε θ, α, K, ?_⟩
  · simpa only [r, t, ε, τ, θ, s₀,
      paperCoalescedState_eq_coalescedFiniteState] using hfamily
  · simpa only [r, t, ε, τ, θ, s₀,
      paperCoalescedState_eq_coalescedFiniteState] using hselected

end
end PhosphorylationStableCapacity
