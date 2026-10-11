module
public import proofs.PhosphorylationStableCapacity.FiniteFixedPrintedContractDefs
public import proofs.PhosphorylationStableCapacity.FiniteFixedPrintedFamily
public import proofs.PhosphorylationStableCapacity.CoalescedFiniteSource

@[expose] public section

namespace PhosphorylationStableCapacity.P079PrintedContract

noncomputable section
open PhosphorylationSharpness Polynomial

/-- The center `M` remains fixed while the recursion descends. This is the
critical correspondence between the independent printed definition and the
arbitrary-offset research recurrence. -/
theorem paperFixedPairAt_eq_arbitrarySplitPair
    (M depth : ℕ) (δ : ℝ) :
    paperFixedPairAt M depth δ =
      arbitrarySplitPair depth (finiteFixedOffset M) δ := by
  induction depth with
  | zero =>
      simp [paperFixedPairAt, arbitrarySplitPair,
        paperFixedRoot, offsetSplitRoot, finiteFixedOffset]
  | succ depth ih =>
      simp [paperFixedPairAt, arbitrarySplitPair, ih,
        paperFixedNextN, paperFixedNextJ, nextN, nextJ,
        paperFixedRoot, offsetSplitRoot, finiteFixedOffset]

theorem paperFixedPair_eq_arbitrarySplitPair (m : ℕ) (δ : ℝ) :
    paperFixedPair m δ =
      arbitrarySplitPair m (finiteFixedOffset m) δ :=
  paperFixedPairAt_eq_arbitrarySplitPair m m δ

theorem paperFixedRadius_eq (m : ℕ) :
    paperFixedRadius m = finiteFixedRadius m := rfl

theorem paperFixedSpacing_eq (m : ℕ) :
    paperFixedSpacing m = finiteFixedSpacing m := rfl

theorem paperFixedRoot_eq_offsetSplitRoot (m j : ℕ) (δ : ℝ) :
    paperFixedRoot m δ j = offsetSplitRoot (finiteFixedOffset m) δ j := rfl

theorem paperFixedRatio_eq (x : ℝ) : paperFixedRatio x = ratio x := rfl

theorem paperFixedRootS_eq (x d : ℝ) :
    paperFixedRootS x d = rootS x d := rfl

theorem paperFixedRootF_eq (x : ℝ) : paperFixedRootF x = rootF x := rfl

/-- Exact converted polynomial identity, including the monic quotient. -/
theorem paperFixedRawD_eq (m : ℕ) (r δ : ℝ) :
    paperFixedRawD m r δ =
      arbitrarySplitRawD m (finiteFixedOffset m) r δ := by
  unfold paperFixedRawD arbitrarySplitRawD
  rw [paperFixedPair_eq_arbitrarySplitPair]
  rfl

theorem paperFixedRawB_eq (m : ℕ) (r δ : ℝ) :
    paperFixedRawB m r δ =
      arbitrarySplitRawB m (finiteFixedOffset m) r δ := by
  unfold paperFixedRawB arbitrarySplitRawB
  rw [paperFixedPair_eq_arbitrarySplitPair, paperFixedRawD_eq]
  rfl

theorem paperFixedT_eq (m : ℕ) (r δ : ℝ) (i : Fin (m + 2)) :
    paperFixedT m r δ i =
      ((1 + X) * arbitrarySplitRawD m (finiteFixedOffset m) r δ).coeff i := by
  rw [paperFixedT, paperFixedRawD_eq]

theorem paperFixedBaseRates_eq (m : ℕ) (r δ : ℝ) :
    paperFixedBaseRates m r δ =
      arbitrarySplitFiniteRates m (finiteFixedOffset m) r δ := by
  simp only [paperFixedBaseRates, arbitrarySplitFiniteRates, realize,
    paperFixedT_eq, paperFixedRawD_eq, paperFixedRawB_eq]

theorem paperFixedCoalescedD_eq (m : ℕ) (i : Fin (m + 1)) :
    paperFixedCoalescedD m i =
      (coalescedFiniteState m (finiteFixedRadius m)).D i := by
  have hD : paperFixedRawD m (paperFixedRadius m) 0 =
      coalescedRawD m (finiteFixedRadius m) := by
    rw [paperFixedRadius_eq, paperFixedRawD_eq,
      arbitrarySplitRawD, arbitrarySplitPair_zero_eq_coalesced]
    rfl
  rw [paperFixedRadius_eq] at hD
  simp only [paperFixedCoalescedD, paperFixedRadius_eq, hD,
    coalescedFiniteState, reconstruct,
    paperFixedRatio_eq, paperFixedRootS_eq, paperFixedRootF_eq]

/-- The independent formula yields exactly the research source's one common
unrelaxed rate vector, including reciprocal coalesced complex scaling. -/
theorem paperFixedRates_eq (m : ℕ) :
    paperFixedRates m = finiteFixedPrintedRates m := by
  simp only [paperFixedRates, finiteFixedPrintedRates,
    paperFixedRadius_eq, paperFixedSpacing_eq,
    paperFixedBaseRates_eq, paperFixedCoalescedD_eq, retune]

/-- Every independent printed state is the same exact state in the source
family; this identity is uniform in site count and equilibrium index. -/
theorem paperFixedState_eq (m : ℕ) (j : Fin (2 * m + 1)) :
    paperFixedState m j = finiteFixedPrintedState m j := by
  simp only [paperFixedState, finiteFixedPrintedState,
    arbitrarySplitFiniteState, reconstruct,
    paperFixedRadius_eq, paperFixedSpacing_eq,
    paperFixedRawD_eq, paperFixedRawB_eq, paperFixedT_eq,
    paperFixedRatio_eq, paperFixedRootS_eq, paperFixedRootF_eq,
    paperFixedRoot_eq_offsetSplitRoot]

theorem paperFixedState_fun_eq (m : ℕ) :
    paperFixedState m = finiteFixedPrintedState m :=
  funext (paperFixedState_eq m)

end
end PhosphorylationStableCapacity.P079PrintedContract
