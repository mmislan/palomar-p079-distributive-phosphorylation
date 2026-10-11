module
public import proofs.PhosphorylationStableCapacity.ArbitraryAllCurrentContinuity435
public import proofs.PhosphorylationStableCapacity.ArbitrarySplitRetunedSource

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section

open PhosphorylationSharpness Polynomial Filter
open scoped Topology

/-- Every positive edge current preserves the arbitrary split source
equilibria and their common conservation class. -/
theorem arbitrarySplitAllCurrentState_source_of_conversion_positive
    (m : ℕ) (ξ : ℕ → ℝ) (r δ ε : ℝ)
    (w : Fin (m+2) → ℝ) (hw : ∀ i, 0 < w i)
    (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hD : DensePositive (arbitrarySplitRawD (m+1) ξ r δ) (m+1))
    (hB : DensePositive (arbitrarySplitRawB (m+1) ξ r δ) (m+1))
    (j : Fin (2*(m+1)+1))
    (hx : 1 < offsetSplitRoot ξ δ j.val) :
    (arbitrarySplitAllCurrentRates m ξ r w δ ε).Positive ∧
      (arbitrarySplitFiniteState (m+1) ξ r δ j).Positive ∧
      Equilibrium (arbitrarySplitAllCurrentRates m ξ r w δ ε)
        (arbitrarySplitFiniteState (m+1) ξ r δ j) ∧
      totalE (arbitrarySplitFiniteState (m+1) ξ r δ j) = 2*r ∧
      totalF (arbitrarySplitFiniteState (m+1) ξ r δ j) = 2 ∧
      totalS (arbitrarySplitFiniteState (m+1) ξ r δ j) = 2*(r+1) := by
  let k := arbitrarySplitFiniteRates (m+1) ξ r δ
  let x := arbitrarySplitFiniteState (m+1) ξ r δ j
  obtain ⟨hk, hxpos, heq, hET, hFT, hST⟩ :=
    arbitrarySplitFiniteState_source_of_conversion_positive
      (m+1) ξ r δ hD hB j hx
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

/-- One fixed positive current vector and binding scale preserves all the
prescribed split equilibria sufficiently close to coalescence. -/
theorem arbitrarySplitAllCurrent_source_eventually
    (m : ℕ) (ξ : ℕ → ℝ) (r ε : ℝ)
    (w : Fin (m+2) → ℝ) (hw : ∀ i, 0 < w i)
    (hr : r ≠ 0) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hD₀ : DensePositive (coalescedRawD (m+1) r) (m+1))
    (hB₀ : DensePositive (coalescedRawB (m+1) r) (m+1)) :
    ∀ᶠ δ : ℝ in 𝓝[>] (0 : ℝ),
      (arbitrarySplitAllCurrentRates m ξ r w δ ε).Positive ∧
      ∀ j : Fin (2*(m+1)+1),
        (arbitrarySplitFiniteState (m+1) ξ r δ j).Positive ∧
        Equilibrium (arbitrarySplitAllCurrentRates m ξ r w δ ε)
          (arbitrarySplitFiniteState (m+1) ξ r δ j) ∧
        totalE (arbitrarySplitFiniteState (m+1) ξ r δ j) = 2*r ∧
        totalF (arbitrarySplitFiniteState (m+1) ξ r δ j) = 2 ∧
        totalS (arbitrarySplitFiniteState (m+1) ξ r δ j) = 2*(r+1) := by
  have hconv := arbitrarySplit_conversion_positive_near_zero
    (m+1) ξ r hr hD₀ hB₀
  have hroot : ∀ᶠ δ : ℝ in 𝓝[>] (0 : ℝ),
      ∀ j, j ≤ 2*(m+1) → 1 < offsetSplitRoot ξ δ j :=
    (offsetSplitRoot_gt_one_eventually (m+1) ξ).filter_mono
      nhdsWithin_le_nhds
  filter_upwards [hconv, hroot] with δ hconv hroot
  have hsource (j : Fin (2*(m+1)+1)) :=
    arbitrarySplitAllCurrentState_source_of_conversion_positive
      m ξ r δ ε w hw hε hε1 hconv.1 hconv.2 j
        (hroot j.val (by omega))
  exact ⟨(hsource 0).1, fun j => (hsource j).2⟩

end

end PhosphorylationStableCapacity
