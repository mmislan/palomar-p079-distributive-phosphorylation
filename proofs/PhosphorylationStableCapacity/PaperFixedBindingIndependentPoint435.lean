module
public import proofs.PhosphorylationStableCapacity.PaperFixedBindingChallengeConstruction435
public import proofs.PhosphorylationStableCapacity.PaperFixedBindingStableSaddleCorollary

@[expose] public section

namespace PhosphorylationStableCapacity
noncomputable section
open PhosphorylationSharpness Polynomial Filter
open scoped Topology

theorem paper_fixed_binding_completePoint_to_signedLawAt
    (m : ℕ) (x : Fin (2*(m+1)+1) → ℝ) (ξ : ℕ → ℝ)
    (hagree : ∀ j : Fin (2*(m+1)+1), ξ j.val=x j)
    (r τ ε α K δ : ℝ) (θ : Fin (m+1) → ℝ)
    (lam : Fin (2*(m+1)+1) → ℝ → ℝ)
    (hr : 0 < r) (hα : 0 < α)
    (hd : PaperFixedBindingCompletePoint m ξ r τ ε α K δ θ lam) :
    PaperFixedBindingSignedLawAt m x ξ r δ ε
      (paperFixedBindingPrintedCoefficient m r τ ε θ) α K
      (Fin.lastCases τ θ) lam := by
  simp only [PaperFixedBindingSignedLawAt,
    paperRates_eq_paperFixedBindingSplitRates,
    paperSourceState_eq_arbitrarySplitFiniteState]
  have hdkeep := hd
  obtain ⟨hkδ, hinj, hexact, hcount, hj⟩ := hd
  refine ⟨hkδ, hinj, hexact, hcount, ?_⟩
  intro j
  obtain ⟨hsδ, heqδ, hETδ, hFTδ, hSTδ, hobs,
    hroot, hsimple, hmargin, hbound, hreciprocal, hneg, hpos⟩ := hj j
  have hgap := paperFiniteGap_eq_sequence_gap x ξ hagree j
  rw [← hgap] at hbound hreciprocal
  rw [hagree j] at hobs
  exact ⟨hsδ, heqδ, ⟨hETδ, hFTδ, hSTδ⟩, hobs, hroot, hsimple,
    hmargin, hbound, hreciprocal, hneg, hpos,
    paperFixedBinding_completePoint_even_nonlinear_sink
      m ξ r τ ε α K δ θ lam hr hα hdkeep j,
    (paperFixedBinding_completePoint_sink_or_saddle
      m ξ r τ ε α K δ θ lam hα hdkeep j).2⟩

end
end PhosphorylationStableCapacity
