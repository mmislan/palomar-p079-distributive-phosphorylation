module
public import proofs.PhosphorylationStableCapacity.FiniteFixedPrintedSource
public import proofs.PhosphorylationStableCapacity.ArbitrarySplitObservable
public import proofs.PhosphorylationStableCapacity.UniversalEquilibriumCount

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section
open PhosphorylationSharpness

theorem finiteFixedOffset_strictMono (m : ℕ) :
    StrictMono (finiteFixedOffset m) := by
  intro i j hij
  exact sub_lt_sub_right (Nat.cast_lt.mpr hij) _

/-- The universal nonhyperbolic ceiling turns the printed injective family
into the complete positive equilibrium set at its one common fixed rate vector. -/
theorem finiteFixedPrinted_positive_equilibria_exact_family
    (m : ℕ) (hr : 0 < finiteFixedRadius m)
    (hδ : 0 < finiteFixedSpacing m)
    (hD : DensePositive
      (arbitrarySplitRawD m (finiteFixedOffset m)
        (finiteFixedRadius m) (finiteFixedSpacing m)) m)
    (hB : DensePositive
      (arbitrarySplitRawB m (finiteFixedOffset m)
        (finiteFixedRadius m) (finiteFixedSpacing m)) m)
    (hcoalD : ∀ i : Fin (m + 1),
      0 < (coalescedFiniteState m (finiteFixedRadius m)).D i)
    (hroot : ∀ j : Fin (2 * m + 1),
      1 < offsetSplitRoot (finiteFixedOffset m)
        (finiteFixedSpacing m) j.val) :
    {x : State (m + 1) |
      x.Positive ∧ Equilibrium (finiteFixedPrintedRates m) x ∧
        InClass (2 * finiteFixedRadius m) 2
          (2 * (finiteFixedRadius m + 1)) x} =
      Set.range (finiteFixedPrintedState m) := by
  let E : Set (State (m + 1)) :=
    {x | x.Positive ∧ Equilibrium (finiteFixedPrintedRates m) x ∧
      InClass (2 * finiteFixedRadius m) 2
        (2 * (finiteFixedRadius m + 1)) x}
  let f : Fin (2 * m + 1) → State (m + 1) := finiteFixedPrintedState m
  have hsource (j : Fin (2 * m + 1)) :=
    finiteFixedPrinted_source_of_coeff_positive
      m hD hB hcoalD j (hroot j)
  have hk : (finiteFixedPrintedRates m).Positive := (hsource 0).1
  have hsubset : Set.range f ⊆ E := by
    rintro x ⟨j, rfl⟩
    exact ⟨(hsource j).2.1, (hsource j).2.2.1,
      (hsource j).2.2.2.1,
      (hsource j).2.2.2.2.1,
      (hsource j).2.2.2.2.2⟩
  have hcap := positive_equilibria_finite_and_ncard_le_two_n_sub_one
    (n := m + 1) (by omega : 0 < m + 1)
    (finiteFixedPrintedRates m) hk
    (2 * finiteFixedRadius m) 2 (2 * (finiteFixedRadius m + 1))
    (by positivity) (by norm_num) (by positivity)
  have hEfin : E.Finite := hcap.1
  have hEle : E.ncard ≤ 2 * m + 1 := by
    have hbound : E.ncard ≤ 2 * (m + 1) - 1 := hcap.2
    omega
  have hfinj : Function.Injective f :=
    arbitrarySplitFiniteState_injective_of_positive_split
      m (finiteFixedOffset m) (finiteFixedOffset_strictMono m)
      (finiteFixedRadius m) (finiteFixedSpacing m) hδ hroot
  have hRcard : (Set.range f).ncard = 2 * m + 1 := by
    simpa [f] using Set.ncard_range_of_injective hfinj
  have hRle : E.ncard ≤ (Set.range f).ncard := by
    rw [hRcard]
    exact hEle
  have heq : Set.range f = E :=
    Set.eq_of_subset_of_ncard_le hsubset hRle hEfin
  exact heq.symm

end
end PhosphorylationStableCapacity
