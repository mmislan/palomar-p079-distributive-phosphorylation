module
public import proofs.PhosphorylationStableCapacity.PaperFixedBindingChallengeResearchDefs
public import proofs.PhosphorylationStableCapacity.PaperFixedBindingSplitCount435
public import proofs.PhosphorylationStableCapacity.FiniteOffsetGapBridge

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section
open PhosphorylationSharpness Polynomial

theorem paperCoalescedPair_eq_coalescedPair (m : ℕ) :
    paperCoalescedPair m = coalescedPair m := by
  induction m with
  | zero => rfl
  | succ m ih =>
    simp only [paperCoalescedPair, coalescedPair, ih, paperNextN,
      paperNextJ, nextN, nextJ]

theorem paperSplitPair_eq_arbitrarySplitPair
    (m : ℕ) (ξ : ℕ → ℝ) (δ : ℝ) :
    paperSplitPair m ξ δ = arbitrarySplitPair m ξ δ := by
  induction m with
  | zero => rfl
  | succ m ih =>
    simp only [paperSplitPair, arbitrarySplitPair, ih, paperNextN,
      paperNextJ, nextN, nextJ, paperOffsetRoot, offsetSplitRoot]

theorem paperRawD_eq_rawD (p q : ℝ[X]) (r : ℝ) :
    paperRawD p q r = rawD p q r := rfl

theorem paperRawB_eq_rawB (p q : ℝ[X]) (r : ℝ) :
    paperRawB p q r = rawB p q r := rfl

theorem paperSplitD_eq_arbitrarySplitRawD
    (m : ℕ) (ξ : ℕ → ℝ) (r δ : ℝ) :
    paperSplitD m ξ r δ = arbitrarySplitRawD m ξ r δ := by
  simp only [paperSplitD, arbitrarySplitRawD,
    paperSplitPair_eq_arbitrarySplitPair, paperRawD_eq_rawD]

theorem paperSplitB_eq_arbitrarySplitRawB
    (m : ℕ) (ξ : ℕ → ℝ) (r δ : ℝ) :
    paperSplitB m ξ r δ = arbitrarySplitRawB m ξ r δ := by
  simp only [paperSplitB, arbitrarySplitRawB,
    paperSplitPair_eq_arbitrarySplitPair, paperRawB_eq_rawB]

theorem paperCoalescedD_eq_coalescedRawD (m : ℕ) (r : ℝ) :
    paperCoalescedD m r = coalescedRawD m r := by
  simp only [paperCoalescedD, coalescedRawD,
    paperCoalescedPair_eq_coalescedPair, paperRawD_eq_rawD]

theorem paperCoalescedB_eq_coalescedRawB (m : ℕ) (r : ℝ) :
    paperCoalescedB m r = coalescedRawB m r := by
  simp only [paperCoalescedB, coalescedRawB,
    paperCoalescedPair_eq_coalescedPair, paperRawB_eq_rawB]

theorem paperSourceRates_eq_arbitrarySplitFiniteRates
    (m : ℕ) (ξ : ℕ → ℝ) (r δ : ℝ) :
    paperSourceRates m ξ r δ = arbitrarySplitFiniteRates (m+1) ξ r δ := by
  simp only [paperSourceRates, arbitrarySplitFiniteRates,
    paperSplitD_eq_arbitrarySplitRawD, paperSplitB_eq_arbitrarySplitRawB]
  rfl

theorem paperSourceState_eq_arbitrarySplitFiniteState
    (m : ℕ) (ξ : ℕ → ℝ) (r δ : ℝ) :
    paperSourceState m ξ r δ = arbitrarySplitFiniteState (m+1) ξ r δ := by
  funext j
  simp only [paperSourceState, arbitrarySplitFiniteState,
    paperSplitD_eq_arbitrarySplitRawD, paperSplitB_eq_arbitrarySplitRawB]
  rfl

theorem paperCoalescedState_eq_coalescedFiniteState (m : ℕ) (r : ℝ) :
    paperCoalescedState m r = coalescedFiniteState (m+1) r := by
  simp only [paperCoalescedState, coalescedFiniteState,
    paperCoalescedD_eq_coalescedRawD, paperCoalescedB_eq_coalescedRawB]
  rfl

theorem paperFixBinding_eq_paperFixedBindingRates {n : ℕ} (k : Rates n) :
    paperFixBinding k = paperFixedBindingRates k := by
  simp only [paperFixBinding, paperFixedBindingRates,
    sourceBindingP_castSucc, sourceBindingQ_succ]

theorem paperRates_eq_paperFixedBindingSplitRates
    (m : ℕ) (ξ : ℕ → ℝ) (r δ ε : ℝ) (w : Fin (m+2) → ℝ) :
    paperRates m ξ r δ ε w = paperFixedBindingSplitRates m ξ r δ ε w := by
  simp only [paperRates, paperFixedBindingSplitRates,
    paperSourceRates_eq_arbitrarySplitFiniteRates,
    paperFixBinding_eq_paperFixedBindingRates]
  rfl

theorem paperFiniteGap_eq_finiteOffsetGap {N : ℕ}
    (x : Fin N → ℝ) (j : Fin N) :
    paperFiniteGap x j = finiteOffsetGap x j := rfl

theorem paperFiniteGap_eq_sequence_gap {N : ℕ}
    (x : Fin N → ℝ) (ξ : ℕ → ℝ)
    (hagree : ∀ j : Fin N, ξ j.val = x j) (j : Fin N) :
    paperFiniteGap x j =
      ∏ i ∈ (Finset.range N).erase j.val, (ξ j.val-ξ i) :=
  (paperFiniteGap_eq_finiteOffsetGap x j).trans
    (finiteOffsetGap_eq_sequence_gap x ξ hagree j)

end
end PhosphorylationStableCapacity
