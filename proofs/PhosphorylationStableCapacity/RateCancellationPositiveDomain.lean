module
public import proofs.PhosphorylationStableCapacity.RateCancellationDifferentiability
public import proofs.PhosphorylationStableCapacity.ClassPolytopeTopology

@[expose] public section

namespace PhosphorylationStableCapacity

open PhosphorylationSharpness

noncomputable section

/-- Strict class coordinates are exactly positive literal states after
reconstruction in loaded coordinates. -/
theorem stateFromLoaded_positive_iff_strict {n : ℕ}
    (ET FT ST : ℝ) (u : CoordinateSpace n) :
    (stateFromLoaded ET FT ST u).Positive ↔
      fromLoadedCoord u ∈ classPolytopeStrict n ET FT ST := by
  constructor
  · intro hx
    have hclass := unChart_inClass ET FT ST
      (ofCoordinateSpace (fromLoadedCoord u))
    have h := positive_state_mem_classPolytopeStrict ET FT ST
      (stateFromLoaded ET FT ST u) hx hclass
    simpa [stateFromLoaded, chart_unChart, to_ofCoordinateSpace] using h
  · rintro ⟨hS, hC, hD, hST, hET, hFT⟩
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro j
      cases j using Fin.cases with
      | zero =>
          change 0 < ST - (∑ i, (fromLoadedCoord u).1 i) -
            (∑ i, (fromLoadedCoord u).2.1 i) -
            (∑ i, (fromLoadedCoord u).2.2 i)
          linarith
      | succ i =>
          exact hS i
    · change 0 < ET - ∑ i, (fromLoadedCoord u).2.1 i
      linarith
    · change 0 < FT - ∑ i, (fromLoadedCoord u).2.2 i
      linarith
    · exact hC
    · exact hD

/-- The positive domain of the exact loaded compatibility-class chart is open. -/
theorem isOpen_stateFromLoaded_positive {n : ℕ}
    (ET FT ST : ℝ) :
    IsOpen {u : CoordinateSpace n |
      (stateFromLoaded ET FT ST u).Positive} := by
  have hcont : Continuous (fromLoadedCoord (n := n)) := by
    have heq : ((loadedCoordContinuous n).symm :
        CoordinateSpace n → CoordinateSpace n) = fromLoadedCoord := by
      funext z
      exact loadedCoordContinuous_symm_apply z
    rw [← heq]
    exact (loadedCoordContinuous n).symm.continuous
  have heq : {u : CoordinateSpace n |
      (stateFromLoaded ET FT ST u).Positive} =
      fromLoadedCoord ⁻¹' classPolytopeStrict n ET FT ST := by
    ext u
    exact stateFromLoaded_positive_iff_strict ET FT ST u
  rw [heq]
  exact (classPolytopeStrict_isOpen n ET FT ST).preimage hcont

end
end PhosphorylationStableCapacity
