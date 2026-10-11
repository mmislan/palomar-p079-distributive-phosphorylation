module
public import proofs.PhosphorylationStableCapacity.PaperFixedBindingRealization435
public import proofs.PhosphorylationStableCapacity.ArbitraryAllCurrentSource435
public import proofs.PhosphorylationStableCapacity.ArbitrarySplitObservable
public import proofs.PhosphorylationStableCapacity.UniversalEquilibriumCount

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section

open PhosphorylationSharpness

/-- The manuscript's split family: freeze every catalytic scale, set
`bᵢ=βᵢ=1` in the positive rate freedom, then relax reversible binding.
The independent current vector is the same at every prescribed state. -/
def paperFixedBindingSplitRates (m : ℕ) (ξ : ℕ → ℝ)
    (r δ ε : ℝ) (w : Fin (m+2) → ℝ) : Rates (m+2) :=
  relaxRates
    (paperFixedBindingRates
      (edgeScaledRates w (arbitrarySplitFiniteRates (m+1) ξ r δ))) ε

/-- The manuscript's reverse-binding constants are literally one before
relaxation; each catalytic phosphatase scale is the frozen edge factor,
independent of the split distance and equilibrium index. -/
theorem paperFixedBindingSplit_unrelaxed_frozen_scales
    (m : ℕ) (ξ : ℕ → ℝ) (r δ : ℝ)
    (w : Fin (m+2) → ℝ) (i : Fin (m+2)) :
    let k := paperFixedBindingRates
      (edgeScaledRates w (arbitrarySplitFiniteRates (m+1) ξ r δ))
    k.b i = 1 ∧ k.beta i = 1 ∧ k.gamma i = w i := by
  simp [paperFixedBindingRates, edgeScaledRates,
    arbitrarySplitFiniteRates, realize]

theorem paperFixedBindingSplit_source
    (m : ℕ) (ξ : ℕ → ℝ) (r δ ε : ℝ)
    (w : Fin (m+2) → ℝ) (hw : ∀ i, 0 < w i)
    (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hD : DensePositive (arbitrarySplitRawD (m+1) ξ r δ) (m+1))
    (hB : DensePositive (arbitrarySplitRawB (m+1) ξ r δ) (m+1))
    (j : Fin (2*(m+1)+1))
    (hx : 1 < offsetSplitRoot ξ δ j.val) :
    (paperFixedBindingSplitRates m ξ r δ ε w).Positive ∧
      (arbitrarySplitFiniteState (m+1) ξ r δ j).Positive ∧
      Equilibrium (paperFixedBindingSplitRates m ξ r δ ε w)
        (arbitrarySplitFiniteState (m+1) ξ r δ j) ∧
      InClass (2*r) 2 (2*(r+1))
        (arbitrarySplitFiniteState (m+1) ξ r δ j) := by
  let k₀ := edgeScaledRates w (arbitrarySplitFiniteRates (m+1) ξ r δ)
  let x := arbitrarySplitFiniteState (m+1) ξ r δ j
  obtain ⟨hk, hxpos, heq, hET, hFT, hST⟩ :=
    arbitrarySplitFiniteState_source_of_conversion_positive
      (m+1) ξ r δ hD hB j hx
  have hk₀ : k₀.Positive := edgeScaledRates_positive w _ hw hk
  have hC (i : Fin (m+2)) :
      kinaseNet (arbitrarySplitFiniteRates (m+1) ξ r δ) x i =
        (arbitrarySplitFiniteRates (m+1) ξ r δ).c i*x.C i := by
    have h := heq.2.2.2.1 i
    dsimp [field] at h
    linarith
  have hD' (i : Fin (m+2)) :
      phosphataseNet (arbitrarySplitFiniteRates (m+1) ξ r δ) x i =
        (arbitrarySplitFiniteRates (m+1) ξ r δ).gamma i*x.D i := by
    have h := heq.2.2.2.2 i
    dsimp [field] at h
    linarith
  have hcat (i : Fin (m+2)) :
      (arbitrarySplitFiniteRates (m+1) ξ r δ).c i*x.C i =
        (arbitrarySplitFiniteRates (m+1) ξ r δ).gamma i*x.D i :=
    equilibrium_catalytic_balance _ _ heq i
  have heq₀ : Equilibrium k₀ x :=
    edgeScaledRates_equilibrium w _ x hC hD' hcat
  have heqpaper : Equilibrium (paperFixedBindingRates k₀) x :=
    paperFixedBindingRates_preserves_equilibrium k₀ x hk₀ heq₀
  refine ⟨relaxRates_positive _
    (paperFixedBindingRates_positive k₀ hk₀) hε hε1,
      hxpos, ?_, ?_⟩
  · exact relaxRates_preserves_equilibrium _ _ (ne_of_gt hε) heqpaper
  · exact ⟨hET, hFT, hST⟩

/-- The `bᵢ=βᵢ=1` rate family has exactly the prescribed split states
as its entire positive class equilibrium set. -/
theorem paperFixedBindingSplit_positive_equilibria_exact_family
    (m : ℕ) (ξ : ℕ → ℝ) (hξ : StrictMono ξ)
    (r τ δ ε : ℝ) (ω : Fin (m+1) → ℝ)
    (hr : 0 < r) (hτ : 0 < τ)
    (hω : ∀ i, 0 < ω i)
    (hδ : 0 < δ) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hD : DensePositive (arbitrarySplitRawD (m+1) ξ r δ) (m+1))
    (hB : DensePositive (arbitrarySplitRawB (m+1) ξ r δ) (m+1))
    (hy : ∀ j : Fin (2*(m+1)+1),
      1 < offsetSplitRoot ξ δ j.val) :
    {x : State (m+2) |
      x.Positive ∧
        Equilibrium (paperFixedBindingSplitRates m ξ r δ ε
          (Fin.lastCases τ ω)) x ∧
        InClass (2*r) 2 (2*(r+1)) x} =
      Set.range (arbitrarySplitFiniteState (m+1) ξ r δ) := by
  let w : Fin (m+2) → ℝ := Fin.lastCases τ ω
  let k := paperFixedBindingSplitRates m ξ r δ ε w
  let f : Fin (2*(m+1)+1) → State (m+2) :=
    arbitrarySplitFiniteState (m+1) ξ r δ
  let E : Set (State (m+2)) :=
    {x | x.Positive ∧ Equilibrium k x ∧
      InClass (2*r) 2 (2*(r+1)) x}
  have hw : ∀ i : Fin (m+2), 0 < w i := by
    intro i
    cases i using Fin.lastCases with
    | last => simpa [w] using hτ
    | cast i => simpa [w] using hω i
  have hsource (j : Fin (2*(m+1)+1)) :=
    paperFixedBindingSplit_source m ξ r δ ε w hw hε hε1
      hD hB j (hy j)
  have hk : k.Positive := (hsource 0).1
  have hsubset : Set.range f ⊆ E := by
    rintro x ⟨j, rfl⟩
    exact ⟨(hsource j).2.1, (hsource j).2.2.1,
      (hsource j).2.2.2⟩
  have hcap := positive_equilibria_finite_and_ncard_le_two_n_sub_one
    (n := m+2) (by omega : 0 < m+2) k hk
    (2*r) 2 (2*(r+1))
    (by positivity) (by norm_num) (by positivity)
  have hEfin : E.Finite := hcap.1
  have hEle : E.ncard ≤ 2*(m+1)+1 := by
    have hbound : E.ncard ≤ 2*(m+2)-1 := hcap.2
    omega
  have hfinj : Function.Injective f :=
    arbitrarySplitFiniteState_injective_of_positive_split
      (m+1) ξ hξ r δ hδ hy
  have hRcard : (Set.range f).ncard = 2*(m+1)+1 := by
    simpa [f] using Set.ncard_range_of_injective hfinj
  have hRle : E.ncard ≤ (Set.range f).ncard := by
    rw [hRcard]
    exact hEle
  have heq : Set.range f = E :=
    Set.eq_of_subset_of_ncard_le hsubset hRle hEfin
  exact heq.symm

end

end PhosphorylationStableCapacity
