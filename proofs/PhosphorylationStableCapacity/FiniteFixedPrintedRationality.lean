module
public import proofs.PhosphorylationStableCapacity.ArbitrarySplitRationalSource
public import proofs.PhosphorylationStableCapacity.FiniteFixedPrintedFamily
public import proofs.PhosphorylationStableCapacity.ArbitrarySplitRetunedSource

@[expose] public section

namespace PhosphorylationStableCapacity
noncomputable section
open PhosphorylationSharpness

/-- Rationality of the printed centered offsets and unrelaxed common rates
is uniform in size; it requires no enumeration of the 48 states. -/
theorem finiteFixedPrinted_rational (m : ℕ) :
    RationalRates (finiteFixedPrintedRates m) ∧
      ∀ j : Fin (2*m+1), RationalState (finiteFixedPrintedState m j) := by
  have hr : RationalReal (finiteFixedRadius m) := by
    unfold finiteFixedRadius
    split_ifs
    · exact ⟨2, by norm_num⟩
    · exact ⟨4, by norm_num⟩
    · exact ⟨8, by norm_num⟩
  have hδ : RationalReal (finiteFixedSpacing m) := by
    unfold finiteFixedSpacing
    split_ifs
    · exact ⟨(1/2 : ℚ), by norm_num⟩
    · exact ⟨(1/4 : ℚ), by norm_num⟩
  have hξ (j : ℕ) : RationalReal (finiteFixedOffset m j) := by
    refine ⟨(j : ℚ)-(m : ℚ), ?_⟩
    push_cast
    rfl
  have hsplit := arbitrarySplitFiniteSource_rational m (finiteFixedOffset m) hr hδ hξ
  have hx₀ : RationalState (coalescedFiniteState m (finiteFixedRadius m)) := by
    have h := (arbitrarySplitFiniteSource_rational m (finiteFixedOffset m)
      hr (show RationalReal (0 : ℝ) from ⟨0, by norm_num⟩) hξ).2
        (0 : Fin (2*m+1))
    rw [arbitrarySplitFiniteState_zero_eq_coalesced] at h
    exact h
  have hl (i : Fin (m+1)) :
      RationalReal (1/(coalescedFiniteState m (finiteFixedRadius m)).D i) := by
    obtain ⟨q, hq⟩ := hx₀.2.2.2.2 i
    refine ⟨1/q, ?_⟩
    push_cast
    rw [hq]
  exact ⟨retune_rational _ _ _ _ hsplit.1 hl
    (fun _ => ⟨1, by norm_num⟩) (fun _ => ⟨1, by norm_num⟩), hsplit.2⟩

end
end PhosphorylationStableCapacity
