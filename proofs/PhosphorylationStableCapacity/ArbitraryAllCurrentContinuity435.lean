module
public import proofs.PhosphorylationStableCapacity.AllCurrentWeightedDerivative435
public import proofs.PhosphorylationStableCapacity.ArbitrarySplitJacobianContinuity

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section

open PhosphorylationSharpness Polynomial Filter
open scoped Topology

/-- Retune every edge of the arbitrary-offset split family by one common
positive current vector, then relax binding by `ε`. -/
def arbitrarySplitAllCurrentRates (m : ℕ) (ξ : ℕ → ℝ)
    (r : ℝ) (w : Fin (m+2) → ℝ) (δ ε : ℝ) : Rates (m+2) :=
  relaxRates (edgeScaledRates w
    (arbitrarySplitFiniteRates (m+1) ξ r δ)) ε

theorem arbitrarySplitAllCurrentRates_zero_eq_coalesced
    (m : ℕ) (ξ : ℕ → ℝ) (r : ℝ)
    (w : Fin (m+2) → ℝ) (ε : ℝ) :
    arbitrarySplitAllCurrentRates m ξ r w 0 ε =
      relaxRates (coalescedAllScaledRates m r w) ε := by
  simp [arbitrarySplitAllCurrentRates, coalescedAllScaledRates,
    arbitrarySplitFiniteRates_zero_eq_coalesced]

theorem arbitrarySplitAllCurrent_rateVector_continuousAt
    (m : ℕ) (ξ : ℕ → ℝ) (r : ℝ) (w : Fin (m+2) → ℝ)
    (ε : ℝ) (hr : r ≠ 0)
    (hD₀ : DensePositive (coalescedRawD (m+1) r) (m+1))
    (hB₀ : DensePositive (coalescedRawB (m+1) r) (m+1)) :
    ContinuousAt
      (fun δ => rateVector (arbitrarySplitAllCurrentRates m ξ r w δ ε)) 0 := by
  apply continuousAt_pi.mpr
  intro j
  apply continuousAt_pi.mpr
  intro i
  obtain ⟨ha, hb, hc, hα, hβ, hγ⟩ :=
    arbitrarySplitFiniteRates_components_continuousAt
      (m+1) ξ r hr hD₀ hB₀ i
  have hwa : ContinuousAt (fun δ =>
      w i * (arbitrarySplitFiniteRates (m+1) ξ r δ).a i) 0 :=
    continuousAt_const.mul ha
  have hwb : ContinuousAt (fun δ =>
      w i * (arbitrarySplitFiniteRates (m+1) ξ r δ).b i) 0 :=
    continuousAt_const.mul hb
  have hwc : ContinuousAt (fun δ =>
      w i * (arbitrarySplitFiniteRates (m+1) ξ r δ).c i) 0 :=
    continuousAt_const.mul hc
  have hwα : ContinuousAt (fun δ =>
      w i * (arbitrarySplitFiniteRates (m+1) ξ r δ).alpha i) 0 :=
    continuousAt_const.mul hα
  have hwβ : ContinuousAt (fun δ =>
      w i * (arbitrarySplitFiniteRates (m+1) ξ r δ).beta i) 0 :=
    continuousAt_const.mul hβ
  have hwγ : ContinuousAt (fun δ =>
      w i * (arbitrarySplitFiniteRates (m+1) ξ r δ).gamma i) 0 :=
    continuousAt_const.mul hγ
  fin_cases j
  · simpa [rateVector, arbitrarySplitAllCurrentRates, relaxRates,
      edgeScaledRates] using hwa.div_const ε
  · change ContinuousAt
      ((fun δ =>
        (w i * (arbitrarySplitFiniteRates (m+1) ξ r δ).b i +
          w i * (arbitrarySplitFiniteRates (m+1) ξ r δ).c i) / ε) -
        (fun δ => w i * (arbitrarySplitFiniteRates (m+1) ξ r δ).c i)) 0
    exact ((hwb.add hwc).div_const ε).sub hwc
  · simpa [rateVector, arbitrarySplitAllCurrentRates, relaxRates,
      edgeScaledRates] using hwc
  · simpa [rateVector, arbitrarySplitAllCurrentRates, relaxRates,
      edgeScaledRates] using hwα.div_const ε
  · change ContinuousAt
      ((fun δ =>
        (w i * (arbitrarySplitFiniteRates (m+1) ξ r δ).beta i +
          w i * (arbitrarySplitFiniteRates (m+1) ξ r δ).gamma i) / ε) -
        (fun δ => w i * (arbitrarySplitFiniteRates (m+1) ξ r δ).gamma i)) 0
    exact ((hwβ.add hwγ).div_const ε).sub hwγ
  · simpa [rateVector, arbitrarySplitAllCurrentRates, relaxRates,
      edgeScaledRates] using hwγ

theorem arbitrarySplitAllCurrent_restrictedJacobianMatrix_continuousAt
    (m : ℕ) (ξ : ℕ → ℝ) (r : ℝ) (w : Fin (m+2) → ℝ)
    (ε : ℝ) (hr : r ≠ 0)
    (hD₀ : DensePositive (coalescedRawD (m+1) r) (m+1))
    (hB₀ : DensePositive (coalescedRawB (m+1) r) (m+1))
    (j : Fin (2*(m+1)+1)) :
    ContinuousAt (fun δ => restrictedJacobianMatrix (2*r) 2 (2*(r+1))
      (arbitrarySplitAllCurrentRates m ξ r w δ ε)
      (toCoordinateSpace (chart
        (arbitrarySplitFiniteState (m+1) ξ r δ j)))) 0 := by
  have hk := arbitrarySplitAllCurrent_rateVector_continuousAt
    m ξ r w ε hr hD₀ hB₀
  have hu := arbitrarySplitState_coordinate_continuousAt
    m ξ r hr hD₀ j
  have h := (continuous_restrictedJacobian_fromVector
    (n := m+2) (2*r) 2 (2*(r+1))).continuousAt.comp (hk.prodMk hu)
  have hJ : ContinuousAt (fun δ => restrictedJacobian (2*r) 2 (2*(r+1))
      (arbitrarySplitAllCurrentRates m ξ r w δ ε)
      (toCoordinateSpace (chart
        (arbitrarySplitFiniteState (m+1) ξ r δ j)))) 0 := by
    simpa [Function.comp_def, ratesFromVector_rateVector] using h
  exact (continuous_coordinateJacobian_matrix (m+2)).continuousAt.comp hJ

theorem arbitrarySplitAllCurrent_restrictedJacobianMatrix_zero_eq_coalesced
    (m : ℕ) (ξ : ℕ → ℝ) (r : ℝ) (w : Fin (m+2) → ℝ)
    (ε : ℝ) (j : Fin (2*(m+1)+1)) :
    restrictedJacobianMatrix (2*r) 2 (2*(r+1))
      (arbitrarySplitAllCurrentRates m ξ r w 0 ε)
      (toCoordinateSpace (chart
        (arbitrarySplitFiniteState (m+1) ξ r 0 j))) =
    restrictedJacobianMatrix (2*r) 2 (2*(r+1))
      (relaxRates (coalescedAllScaledRates m r w) ε)
      (fromLoadedCoord (loadedCoordOfState
        (coalescedFiniteState (m+1) r))) := by
  rw [arbitrarySplitAllCurrentRates_zero_eq_coalesced,
    arbitrarySplitFiniteState_zero_eq_coalesced]
  simp only [loadedCoordOfState, from_toLoadedCoord]

end

end PhosphorylationStableCapacity
