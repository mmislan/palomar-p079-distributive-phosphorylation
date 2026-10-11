module
public import proofs.PhosphorylationStableCapacity.SplitSourceContinuity
public import proofs.PhosphorylationStableCapacity.CoalescedFinalRateRetune
public import proofs.PhosphorylationStableCapacity.BoundaryEquilibrium
public import proofs.PhosphorylationStableCapacity.RelaxationRates

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section

open PhosphorylationSharpness Polynomial

/-- Explicit admissibility of one state in the split family, before the
equilibrium-preserving kinetic retunings. -/
theorem splitFiniteState_source_of_conversion_positive
    (m : ℕ) (r δ : ℝ) (hδ : 0 ≤ δ)
    (hD : DensePositive (splitRawD m r δ) m)
    (hB : DensePositive (splitRawB m r δ) m)
    (j : Fin (2*m+1)) :
    (splitFiniteRates m r δ).Positive ∧
      (splitFiniteState m r δ j).Positive ∧
      Equilibrium (splitFiniteRates m r δ) (splitFiniteState m r δ j) ∧
      totalE (splitFiniteState m r δ j) = 2*r ∧
      totalF (splitFiniteState m r δ j) = 2 ∧
      totalS (splitFiniteState m r δ j) = 2*(r+1) := by
  let x := splitRoot δ j.val
  have hx : 1 < x := by
    have hh : 0 ≤ δ * (j.val : ℝ) :=
      mul_nonneg hδ (Nat.cast_nonneg _)
    dsimp [x, splitRoot]
    linarith
  have hroot := splitPair_roots m j.val δ (by omega)
  have hrel := conversion_root (splitPair m δ).1 (splitPair m δ).2
    r x hroot
  have hstate := source_from_coefficients (splitRawB m r δ)
    (splitRawD m r δ) hB hD r x hx hrel
  have hA := dense_inventory_product hD
  have hrate : (splitFiniteRates m r δ).Positive := by
    apply realize_positive
    · intro i
      exact hA.1 i (by omega)
    · intro i
      exact hB.1 i (by omega)
    · intro i
      exact hD.1 i (by omega)
  exact ⟨hrate, by simpa only [splitFiniteState, x] using hstate.1,
    by simpa only [splitFiniteRates, splitFiniteState, x] using hstate.2.1,
    by simpa only [splitFiniteState, x] using hstate.2.2.1,
    by simpa only [splitFiniteState, x] using hstate.2.2.2.1,
    by simpa only [splitFiniteState, x] using hstate.2.2.2.2⟩

/-- Final-edge retuning and fast binding are applied to one common split
rate list; no equilibrium-dependent rate choice occurs. -/
def splitRetunedRates (m : ℕ) (r τ δ ε : ℝ) : Rates (m + 2) :=
  relaxRates
    (edgeScaledRates (coalescedFinalCurrentWeights m τ)
      (splitFiniteRates (m + 1) r δ)) ε

theorem splitRetunedRates_zero_eq_coalesced (m : ℕ) (r τ ε : ℝ) :
    splitRetunedRates m r τ 0 ε =
      relaxRates (coalescedFinalScaledRates m r τ) ε := by
  simp [splitRetunedRates, coalescedFinalScaledRates,
    splitFiniteRates_zero_eq_coalesced]

/-- Every split state remains a positive equilibrium for the very same
retuned and relaxed rate list, with the same three totals. -/
theorem splitRetunedState_source_of_conversion_positive
    (m : ℕ) (r τ δ ε : ℝ)
    (hτ : 0 < τ) (hδ : 0 ≤ δ) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hD : DensePositive (splitRawD (m+1) r δ) (m+1))
    (hB : DensePositive (splitRawB (m+1) r δ) (m+1))
    (j : Fin (2*(m+1)+1)) :
    (splitRetunedRates m r τ δ ε).Positive ∧
      (splitFiniteState (m+1) r δ j).Positive ∧
      Equilibrium (splitRetunedRates m r τ δ ε)
        (splitFiniteState (m+1) r δ j) ∧
      totalE (splitFiniteState (m+1) r δ j) = 2*r ∧
      totalF (splitFiniteState (m+1) r δ j) = 2 ∧
      totalS (splitFiniteState (m+1) r δ j) = 2*(r+1) := by
  let k := splitFiniteRates (m+1) r δ
  let x := splitFiniteState (m+1) r δ j
  obtain ⟨hk, hx, heq, hET, hFT, hST⟩ :=
    splitFiniteState_source_of_conversion_positive (m+1) r δ hδ hD hB j
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
  exact ⟨relaxRates_positive _ hscaled hε hε1, hx,
    relaxRates_preserves_equilibrium _ _ (ne_of_gt hε) heqscaled,
    hET, hFT, hST⟩

end
end PhosphorylationStableCapacity
