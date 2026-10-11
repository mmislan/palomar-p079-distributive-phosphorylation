module
public import proofs.PhosphorylationStableCapacity.ArbitrarySplitSource
public import proofs.PhosphorylationStableCapacity.SplitRetunedSource

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section

open PhosphorylationSharpness Polynomial

theorem arbitrarySplitFiniteRates_zero_eq_coalesced
    (m : ℕ) (ξ : ℕ → ℝ) (r : ℝ) :
    arbitrarySplitFiniteRates m ξ r 0 = coalescedFiniteRates m r := by
  simp [arbitrarySplitFiniteRates, arbitrarySplitRawD, arbitrarySplitRawB,
    coalescedFiniteRates, coalescedRawD, coalescedRawB,
    arbitrarySplitPair_zero_eq_coalesced]

theorem arbitrarySplitFiniteState_zero_eq_coalesced
    (m : ℕ) (ξ : ℕ → ℝ) (r : ℝ) (j : Fin (2*m+1)) :
    arbitrarySplitFiniteState m ξ r 0 j = coalescedFiniteState m r := by
  simp [arbitrarySplitFiniteState, arbitrarySplitRawD, arbitrarySplitRawB,
    coalescedFiniteState, coalescedRawD, coalescedRawB,
    arbitrarySplitPair_zero_eq_coalesced, offsetSplitRoot]

/-- The source family at arbitrary prescribed offsets uses the same frozen
final-edge current and binding scales as its coalesced system. -/
def arbitrarySplitRetunedRates (m : ℕ) (ξ : ℕ → ℝ)
    (r τ δ ε : ℝ) : Rates (m+2) :=
  relaxRates
    (edgeScaledRates (coalescedFinalCurrentWeights m τ)
      (arbitrarySplitFiniteRates (m+1) ξ r δ)) ε

theorem arbitrarySplitRetunedRates_zero_eq_coalesced
    (m : ℕ) (ξ : ℕ → ℝ) (r τ ε : ℝ) :
    arbitrarySplitRetunedRates m ξ r τ 0 ε =
      relaxRates (coalescedFinalScaledRates m r τ) ε := by
  simp [arbitrarySplitRetunedRates, coalescedFinalScaledRates,
    arbitrarySplitFiniteRates_zero_eq_coalesced]

theorem arbitrarySplitRetunedState_source_of_conversion_positive
    (m : ℕ) (ξ : ℕ → ℝ) (r τ δ ε : ℝ)
    (hτ : 0 < τ) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hD : DensePositive (arbitrarySplitRawD (m+1) ξ r δ) (m+1))
    (hB : DensePositive (arbitrarySplitRawB (m+1) ξ r δ) (m+1))
    (j : Fin (2*(m+1)+1))
    (hx : 1 < offsetSplitRoot ξ δ j.val) :
    (arbitrarySplitRetunedRates m ξ r τ δ ε).Positive ∧
      (arbitrarySplitFiniteState (m+1) ξ r δ j).Positive ∧
      Equilibrium (arbitrarySplitRetunedRates m ξ r τ δ ε)
        (arbitrarySplitFiniteState (m+1) ξ r δ j) ∧
      totalE (arbitrarySplitFiniteState (m+1) ξ r δ j) = 2*r ∧
      totalF (arbitrarySplitFiniteState (m+1) ξ r δ j) = 2 ∧
      totalS (arbitrarySplitFiniteState (m+1) ξ r δ j) = 2*(r+1) := by
  let k := arbitrarySplitFiniteRates (m+1) ξ r δ
  let x := arbitrarySplitFiniteState (m+1) ξ r δ j
  obtain ⟨hk, hxpos, heq, hET, hFT, hST⟩ :=
    arbitrarySplitFiniteState_source_of_conversion_positive
      (m+1) ξ r δ hD hB j hx
  let w := coalescedFinalCurrentWeights m τ
  have hw (i : Fin (m+2)) : 0 < w i := by
    by_cases hi : i = Fin.last (m+1)
    · simp [w, coalescedFinalCurrentWeights, hi, hτ]
    · simp [w, coalescedFinalCurrentWeights, hi]
  have hscaled : (edgeScaledRates w k).Positive :=
    edgeScaledRates_positive w k hw hk
  have hC (i : Fin (m+2)) : kinaseNet k x i = k.c i * x.C i := by
    have h := heq.2.2.2.1 i
    dsimp [field] at h
    linarith
  have hY (i : Fin (m+2)) :
      phosphataseNet k x i = k.gamma i * x.D i := by
    have h := heq.2.2.2.2 i
    dsimp [field] at h
    linarith
  have hcat (i : Fin (m+2)) : k.c i * x.C i = k.gamma i * x.D i :=
    equilibrium_catalytic_balance k x heq i
  have heqscaled : Equilibrium (edgeScaledRates w k) x :=
    edgeScaledRates_equilibrium w k x hC hY hcat
  exact ⟨relaxRates_positive _ hscaled hε hε1, hxpos,
    relaxRates_preserves_equilibrium _ _ (ne_of_gt hε) heqscaled,
    hET, hFT, hST⟩

end
end PhosphorylationStableCapacity
