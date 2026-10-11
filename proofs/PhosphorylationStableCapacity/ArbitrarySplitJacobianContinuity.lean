module
public import proofs.PhosphorylationStableCapacity.ArbitrarySplitStateContinuity
public import proofs.PhosphorylationStableCapacity.SplitJacobianContinuity

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section

open PhosphorylationSharpness Polynomial Filter
open scoped Topology

theorem arbitrarySplitRetuned_rateVector_continuousAt
    (m : ℕ) (ξ : ℕ → ℝ) (r τ ε : ℝ) (hr : r ≠ 0)
    (hD₀ : DensePositive (coalescedRawD (m+1) r) (m+1))
    (hB₀ : DensePositive (coalescedRawB (m+1) r) (m+1)) :
    ContinuousAt
      (fun δ => rateVector (arbitrarySplitRetunedRates m ξ r τ δ ε)) 0 := by
  apply continuousAt_pi.mpr
  intro j
  apply continuousAt_pi.mpr
  intro i
  obtain ⟨ha, hb, hc, hα, hβ, hγ⟩ :=
    arbitrarySplitRetunedRates_components_continuousAt
      m ξ r τ ε hr hD₀ hB₀ i
  fin_cases j <;>
    first
    | simpa [rateVector] using ha
    | simpa [rateVector] using hb
    | simpa [rateVector] using hc
    | simpa [rateVector] using hα
    | simpa [rateVector] using hβ
    | simpa [rateVector] using hγ

theorem arbitrarySplitState_coordinate_continuousAt
    (m : ℕ) (ξ : ℕ → ℝ) (r : ℝ) (hr : r ≠ 0)
    (hD₀ : DensePositive (coalescedRawD (m+1) r) (m+1))
    (j : Fin (2*(m+1)+1)) :
    ContinuousAt (fun δ =>
      toCoordinateSpace (chart
        (arbitrarySplitFiniteState (m+1) ξ r δ j))) 0 := by
  obtain ⟨hS, _, _, hC, hD⟩ :=
    arbitrarySplitFiniteState_components_continuousAt
      (m+1) ξ r hr hD₀ j
  exact (continuousAt_pi.mpr (fun i : Fin (m+2) => hS i.succ)).prodMk
    ((continuousAt_pi.mpr hC).prodMk (continuousAt_pi.mpr hD))

theorem arbitrarySplit_restrictedJacobian_continuousAt
    (m : ℕ) (ξ : ℕ → ℝ) (r τ ε : ℝ) (hr : r ≠ 0)
    (hD₀ : DensePositive (coalescedRawD (m+1) r) (m+1))
    (hB₀ : DensePositive (coalescedRawB (m+1) r) (m+1))
    (j : Fin (2*(m+1)+1)) :
    ContinuousAt (fun δ => restrictedJacobian (2*r) 2 (2*(r+1))
      (arbitrarySplitRetunedRates m ξ r τ δ ε)
      (toCoordinateSpace (chart
        (arbitrarySplitFiniteState (m+1) ξ r δ j)))) 0 := by
  have hk := arbitrarySplitRetuned_rateVector_continuousAt
    m ξ r τ ε hr hD₀ hB₀
  have hu := arbitrarySplitState_coordinate_continuousAt
    m ξ r hr hD₀ j
  have h := (continuous_restrictedJacobian_fromVector
    (n := m+2) (2*r) 2 (2*(r+1))).continuousAt.comp (hk.prodMk hu)
  simpa [Function.comp_def, ratesFromVector_rateVector] using h

theorem arbitrarySplit_restrictedJacobianMatrix_continuousAt
    (m : ℕ) (ξ : ℕ → ℝ) (r τ ε : ℝ) (hr : r ≠ 0)
    (hD₀ : DensePositive (coalescedRawD (m+1) r) (m+1))
    (hB₀ : DensePositive (coalescedRawB (m+1) r) (m+1))
    (j : Fin (2*(m+1)+1)) :
    ContinuousAt (fun δ => restrictedJacobianMatrix (2*r) 2 (2*(r+1))
      (arbitrarySplitRetunedRates m ξ r τ δ ε)
      (toCoordinateSpace (chart
        (arbitrarySplitFiniteState (m+1) ξ r δ j)))) 0 := by
  exact (continuous_coordinateJacobian_matrix (m+2)).continuousAt.comp
    (arbitrarySplit_restrictedJacobian_continuousAt
      m ξ r τ ε hr hD₀ hB₀ j)

theorem arbitrarySplit_restrictedJacobianMatrix_zero_eq_coalesced
    (m : ℕ) (ξ : ℕ → ℝ) (r τ ε : ℝ)
    (j : Fin (2*(m+1)+1)) :
    restrictedJacobianMatrix (2*r) 2 (2*(r+1))
      (arbitrarySplitRetunedRates m ξ r τ 0 ε)
      (toCoordinateSpace (chart
        (arbitrarySplitFiniteState (m+1) ξ r 0 j))) =
    restrictedJacobianMatrix (2*r) 2 (2*(r+1))
      (relaxRates (coalescedFinalScaledRates m r τ) ε)
      (fromLoadedCoord (loadedCoordOfState
        (coalescedFiniteState (m+1) r))) := by
  rw [arbitrarySplitRetunedRates_zero_eq_coalesced,
    arbitrarySplitFiniteState_zero_eq_coalesced]
  simp only [loadedCoordOfState, from_toLoadedCoord]

theorem arbitrarySplit_complexJacobian_continuousAt
    (m : ℕ) (ξ : ℕ → ℝ) (r τ ε : ℝ) (hr : r ≠ 0)
    (hD₀ : DensePositive (coalescedRawD (m+1) r) (m+1))
    (hB₀ : DensePositive (coalescedRawB (m+1) r) (m+1))
    (j : Fin (2*(m+1)+1)) :
    ContinuousAt (fun δ =>
      (restrictedJacobianMatrix (2*r) 2 (2*(r+1))
        (arbitrarySplitRetunedRates m ξ r τ δ ε)
        (toCoordinateSpace (chart
          (arbitrarySplitFiniteState (m+1) ξ r δ j)))).map
            (algebraMap ℝ ℂ)) 0 := by
  exact (continuous_complexification_matrix (m+2)).continuousAt.comp
    (arbitrarySplit_restrictedJacobianMatrix_continuousAt
      m ξ r τ ε hr hD₀ hB₀ j)

end
end PhosphorylationStableCapacity
