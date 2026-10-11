module
public import proofs.PhosphorylationStableCapacity.PaperCompactChallengeResearchDefs
public import proofs.PhosphorylationStableCapacity.PaperFixedBindingChallengeConstruction435
public import proofs.PhosphorylationStableCapacity.CompactActualCurrentPaperPrintedLaw435
public import proofs.PhosphorylationStableCapacity.FiniteOrderedOffsetExtension

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section

open PhosphorylationSharpness Polynomial Filter Matrix
open scoped Topology

/-- Select the independently stated compact-current manuscript law
from the one literal frozen-binding family and its one common signed
split interval. The finite offsets are extended without changing any
listed root. Empty compact current sets retain the global readout
clause. -/
theorem paper_compact_actual_current_law
    (m : ℕ) (x : Fin (2*(m+1)+1) → ℝ) :
    PaperCompactActualCurrentLaw m x := by
  intro hx
  obtain ⟨ξ, hξ, hagree⟩ :=
    finite_ordered_offsets_extend (by omega : 0 < 2*(m+1)+1) x hx
  refine ⟨ξ, hξ, hagree, ?_⟩
  filter_upwards [compactActualCurrent_paperFixedBinding_printed_family
      m ξ hξ, coalescedFiniteState_eventually_equilibrium (m+1)]
    with r hfamily hsource
  intro K hK
  obtain ⟨t, ε, α, Kerr, Cread, ht, hε, hε1, hα, hKerr,
    hCread, hanalytic, hδ⟩ := hfamily K hK
  let X₀ := coalescedFiniteState (m+1) r
  let w (ω : PaperPositivePrefixCurrents m) : Fin (m+2) → ℝ :=
    Fin.lastCases (t/X₀.D (Fin.last (m+1)))
      (fun i => ω.val i/X₀.D i.castSucc)
  let k (ω : PaperPositivePrefixCurrents m) (δ : ℝ) :=
    paperFixedBindingSplitRates m ξ r δ ε (w ω)
  let lam (ω : PaperPositivePrefixCurrents m)
      (j : Fin (2*(m+1)+1)) (δ : ℝ) :=
    selectedTransverseRoot
      (fun (p : Fin (m+2) → ℝ) (s : ℝ) =>
        restrictedJacobianMatrix (2*r) 2 (2*(r+1))
          (paperFixedBindingSplitRates m ξ r s ε p)
          (toCoordinateSpace (chart
            (arbitrarySplitFiniteState (m+1) ξ r s j))))
      α (w ω) δ
  let A (ω : PaperPositivePrefixCurrents m) :=
    paperFixedBindingPrintedCoefficient m r
      (t/X₀.D (Fin.last (m+1))) ε
      (fun i => ω.val i/X₀.D i.castSucc)
  simp only [paperCoalescedState_eq_coalescedFiniteState,
    paperSourceState_eq_arbitrarySplitFiniteState,
    paperRates_eq_paperFixedBindingSplitRates,
    paperCoalescedPair_eq_coalescedPair,
    paperCoalescedD_eq_coalescedRawD,
    paperCoalescedB_eq_coalescedRawB]
  refine ⟨t, ε, α, Kerr, Cread, ht, hε, hε1, hα, hKerr,
    hCread, lam, A, ?_, ?_⟩
  · intro ω hω
    have hpos : X₀.Positive := hsource.2.1
    obtain ⟨δ₀, hδ₀⟩ := hδ.exists
    have hcoeff := hδ₀.2.2 ω hω
    obtain ⟨hprefixδ, hfinalδ, hkδ, hinjδ, hsetδ,
      hcardδ, horderδ, hApos, hAeq, hstatesδ⟩ := hcoeff
    refine ⟨hApos, ?_, ?_, ?_, ?_⟩
    · intro j
      simpa only [lam, w, X₀] using hanalytic ω hω j
    · intro i
      simpa only [k, w, X₀, paperFixedBindingSplitRates,
        arbitrarySplitFiniteRates_zero_eq_coalesced,
        coalescedAllScaledRates, finalEdgeFactorOfActualCurrent,
        edgePrefixFactorsOfActualCurrent] using
        paperFixedBinding_actual_prefix_current_eq m r t ε
          hpos ω i
    · simpa only [k, w, X₀, paperFixedBindingSplitRates,
        arbitrarySplitFiniteRates_zero_eq_coalesced,
        coalescedAllScaledRates, finalEdgeFactorOfActualCurrent,
        edgePrefixFactorsOfActualCurrent] using
        paperFixedBinding_actual_final_current_eq m r t ε
          hpos ω
    · simpa only [A, w, X₀, paperFixedBindingSplitRates,
        arbitrarySplitFiniteRates_zero_eq_coalesced,
        coalescedAllScaledRates] using hAeq
  · filter_upwards [hδ] with δ hd
    obtain ⟨hread, horder, hfor⟩ := hd
    refine ⟨?_, ?_, ?_⟩
    · intro j l
      have h := hread j l
      have hscalar : paperReadoutScalar m (coalescedRawD (m+1) r) =
          splitReadoutScalar (m+1) (coalescedRawD (m+1) r) := by
        funext u
        rfl
      rw [hscalar]
      simpa only [paperReadout, fullyPhosphorylatedReadout,
        hagree j, hagree l] using h
    · simpa only [paperReadout, fullyPhosphorylatedReadout]
        using horder
    · intro ω hω
      obtain ⟨hprefixδ, hfinalδ, hkδ, hinjδ, hsetδ,
        hcardδ, horderδ, hApos, hAeq, hstatesδ⟩ :=
        hfor ω hω
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · simpa only [k, w, X₀] using hkδ
      · simpa only [w, X₀] using hinjδ
      · simpa only [k, w, X₀] using hsetδ
      · simpa only [k, w, X₀] using hcardδ
      · intro j
        obtain ⟨eig, hs, hflux, heq, hclass, hobs,
          han, hzero, hselected, hroot, hsimple, hmargin,
          hrelative, err, herr, hreciprocal, hneg, hpositive,
          hsink, hsaddle⟩ := hstatesδ j
        have hgap := paperFiniteGap_eq_sequence_gap x ξ hagree j
        rw [← hgap] at hrelative hreciprocal
        rw [hagree j] at hobs
        rw [hselected] at hroot hsimple hmargin hrelative hreciprocal hneg hpositive
        refine ⟨hs, ?_, hclass, hobs, ?_, ?_, ?_, ?_, ?_,
          hneg, hpositive, ?_, ?_⟩
        · simpa only [k, w, X₀] using heq
        · simpa only [lam, k, w, X₀] using hroot
        · simpa only [lam, k, w, X₀] using hsimple
        · simpa only [lam, k, w, X₀] using hmargin
        · simpa only [lam, A, k, w, X₀] using hrelative
        · refine ⟨err, herr, ?_⟩
          simpa only [lam, A, k, w, X₀] using hreciprocal
        · simpa only [k, w, X₀] using hsink
        · simpa only [k, w, X₀] using hsaddle

end

end PhosphorylationStableCapacity
