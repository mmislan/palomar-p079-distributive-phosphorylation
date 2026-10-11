module
public import proofs.PhosphorylationStableCapacity.CoalescedSourceSubstrateLimit

@[expose] public section

namespace PhosphorylationStableCapacity

open Filter PhosphorylationSharpness

noncomputable section

/-- The literal coalesced equilibrium has exact complex and free-substrate
totals, not merely asymptotic ones. -/
theorem coalescedFiniteState_eventually_component_totals (m : ℕ) :
    ∀ᶠ r : ℝ in atTop,
      (∑ i, (coalescedFiniteState m r).C i) = 2 * r - 1 ∧
      (∑ i, (coalescedFiniteState m r).D i) = 1 ∧
      (∑ i, (coalescedFiniteState m r).S i) = 2 := by
  filter_upwards [coalescedFiniteState_eventually_equilibrium m] with r h
  obtain ⟨_, _, _, hE, hF, hS⟩ := h
  obtain ⟨hfreeE, hfreeF⟩ := coalescedFiniteState_EF m r
  unfold totalE at hE
  unfold totalF at hF
  unfold totalS at hS
  constructor
  · rw [hfreeE] at hE
    linarith
  constructor
  · rw [hfreeF] at hF
    linarith
  · rw [hfreeE] at hE
    rw [hfreeF] at hF
    linarith

/-- The last free substrate level equals the last phosphatase complex at
every parameter value: the higher raw coefficient vanishes identically. -/
theorem coalescedFiniteState_lastS_eq_lastD (m : ℕ) (r : ℝ) :
    (coalescedFiniteState m r).S (Fin.last (m + 1)) =
      (coalescedFiniteState m r).D (Fin.last m) := by
  have hzero := (raw_support (coalescedPair_dense m).1
    (coalescedPair_dense m).2 r (m + 1) (by omega)).1
  rw [coalescedFiniteState_S_eq]
  norm_num [finiteD, coalescedRawD, hzero, coalescedFiniteState,
    reconstruct, ratio, rootS_three, rootF, div_eq_mul_inv]

end
end PhosphorylationStableCapacity
