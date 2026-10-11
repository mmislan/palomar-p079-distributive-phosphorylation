module
public import proofs.PhosphorylationStableCapacity.FiniteFixedPrintedExactCount
public import proofs.PhosphorylationStableCapacity.FiniteFixedCoefficientBridge
public import proofs.PhosphorylationStableCapacity.FiniteFixedPrintedRationality

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section
open PhosphorylationSharpness

theorem finiteFixedRadius_pos (m : ℕ) : 0 < finiteFixedRadius m := by
  unfold finiteFixedRadius
  split_ifs <;> norm_num

theorem finiteFixedSpacing_pos (m : ℕ) : 0 < finiteFixedSpacing m := by
  unfold finiteFixedSpacing
  split_ifs <;> norm_num

/-- The compact printed construction, once its six finite coefficient and
coalesced-complex checks are discharged, gives positive rates, the complete
common-class equilibrium list, and exact exhaustion by one shared system.
The fixed rates and states are the formulas in `FiniteFixedPrintedFamily`. -/
theorem finiteFixedPrinted_full_source_of_coeff_positive
    (m : ℕ) (hm : 1 ≤ m) (hm6 : m ≤ 6)
    (hD : DensePositive
      (arbitrarySplitRawD m (finiteFixedOffset m)
        (finiteFixedRadius m) (finiteFixedSpacing m)) m)
    (hB : DensePositive
      (arbitrarySplitRawB m (finiteFixedOffset m)
        (finiteFixedRadius m) (finiteFixedSpacing m)) m)
    (hcoalD : ∀ i : Fin (m + 1),
      0 < (coalescedFiniteState m (finiteFixedRadius m)).D i) :
    (finiteFixedPrintedRates m).Positive ∧
      (∀ j : Fin (2 * m + 1),
        (finiteFixedPrintedState m j).Positive ∧
        Equilibrium (finiteFixedPrintedRates m)
          (finiteFixedPrintedState m j) ∧
        InClass (2 * finiteFixedRadius m) 2
          (2 * (finiteFixedRadius m + 1))
          (finiteFixedPrintedState m j)) ∧
      Function.Injective (finiteFixedPrintedState m) ∧
      {x : State (m + 1) |
        x.Positive ∧ Equilibrium (finiteFixedPrintedRates m) x ∧
          InClass (2 * finiteFixedRadius m) 2
            (2 * (finiteFixedRadius m + 1)) x} =
        Set.range (finiteFixedPrintedState m) := by
  have hroot (j : Fin (2 * m + 1)) :
      1 < offsetSplitRoot (finiteFixedOffset m)
        (finiteFixedSpacing m) j.val :=
    finiteFixed_root_gt_one_of_range m hm hm6 j.val
  have hsource (j : Fin (2 * m + 1)) :=
    finiteFixedPrinted_source_of_coeff_positive m hD hB hcoalD j
      (hroot j)
  have hinj : Function.Injective (finiteFixedPrintedState m) :=
    arbitrarySplitFiniteState_injective_of_positive_split
      m (finiteFixedOffset m) (finiteFixedOffset_strictMono m)
      (finiteFixedRadius m) (finiteFixedSpacing m)
      (finiteFixedSpacing_pos m) hroot
  have hexact := finiteFixedPrinted_positive_equilibria_exact_family
    m (finiteFixedRadius_pos m) (finiteFixedSpacing_pos m)
    hD hB hcoalD hroot
  refine ⟨(hsource 0).1, ?_, hinj, hexact⟩
  intro j
  exact ⟨(hsource j).2.1, (hsource j).2.2.1,
    (hsource j).2.2.2.1, (hsource j).2.2.2.2.1,
    (hsource j).2.2.2.2.2⟩

/-- Rationality, the full positive family, and its cardinality share exactly
the same literal printed rates and states. Only the six scalar coefficient
checks remain inputs to this internal assembly theorem. -/
theorem finiteFixedPrinted_complete_source_of_coeff_positive
    (m : ℕ) (hm : 1 ≤ m) (hm6 : m ≤ 6)
    (hD : DensePositive
      (arbitrarySplitRawD m (finiteFixedOffset m)
        (finiteFixedRadius m) (finiteFixedSpacing m)) m)
    (hB : DensePositive
      (arbitrarySplitRawB m (finiteFixedOffset m)
        (finiteFixedRadius m) (finiteFixedSpacing m)) m)
    (hcoalD : ∀ i : Fin (m+1),
      0 < (coalescedFiniteState m (finiteFixedRadius m)).D i) :
    RationalRates (finiteFixedPrintedRates m) ∧
      (finiteFixedPrintedRates m).Positive ∧
      (∀ j : Fin (2*m+1), RationalState (finiteFixedPrintedState m j) ∧
        (finiteFixedPrintedState m j).Positive ∧
        Equilibrium (finiteFixedPrintedRates m) (finiteFixedPrintedState m j) ∧
        InClass (2*finiteFixedRadius m) 2 (2*(finiteFixedRadius m+1))
          (finiteFixedPrintedState m j)) ∧
      Function.Injective (finiteFixedPrintedState m) ∧
      {s : State (m+1) | s.Positive ∧ Equilibrium (finiteFixedPrintedRates m) s ∧
        InClass (2*finiteFixedRadius m) 2 (2*(finiteFixedRadius m+1)) s} =
          Set.range (finiteFixedPrintedState m) ∧
      {s : State (m+1) | s.Positive ∧ Equilibrium (finiteFixedPrintedRates m) s ∧
        InClass (2*finiteFixedRadius m) 2 (2*(finiteFixedRadius m+1)) s}.ncard =
          2*m+1 := by
  obtain ⟨hk, hs, hinj, hexact⟩ :=
    finiteFixedPrinted_full_source_of_coeff_positive m hm hm6 hD hB hcoalD
  obtain ⟨hrat, hstateRat⟩ := finiteFixedPrinted_rational m
  refine ⟨hrat, hk, (fun j => ⟨hstateRat j, hs j⟩), hinj, hexact, ?_⟩
  rw [hexact]
  simpa using Set.ncard_range_of_injective hinj

end
end PhosphorylationStableCapacity
