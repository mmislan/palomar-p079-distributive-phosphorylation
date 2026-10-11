module
public import proofs.PhosphorylationStableCapacity.PaperFixedBindingCompactSecant435
public import proofs.PhosphorylationStableCapacity.PaperFixedBindingJacobianDifferentiability435
public import proofs.PhosphorylationStableCapacity.LoadedJacobianCharpolyBridge

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section

open PhosphorylationSharpness Filter Matrix Polynomial
open scoped Topology

/-- The rectangular characteristic secant estimate specialized to
the actual fixed-binding split state, rate vector, and class Jacobian.
No independently selected comparison matrix occurs in this bound. -/
theorem paperFixedBinding_compact_actual_secant_first_order
    (m : ℕ) (ξ : ℕ → ℝ) (r ε : ℝ)
    (K : Set (Fin (m+2) → ℝ)) (hK : IsCompact K)
    (hKpos : ∀ w ∈ K, ∀ i, 0 < w i)
    (hr : r ≠ 0)
    (hD₀ : DensePositive (coalescedRawD (m+1) r) (m+1))
    (hB₀ : DensePositive (coalescedRawB (m+1) r) (m+1))
    (hbase0 : (coalescedFiniteRates (m+1) r).Positive)
    (hsource : ∀ᶠ δ : ℝ in 𝓝 0,
      (arbitrarySplitFiniteRates (m+1) ξ r δ).Positive)
    (j : Fin (2*(m+1)+1)) :
    ∃ η C : ℝ, 0 < η ∧ 0 < C ∧
      ∀ w ∈ K, ∀ δ x : ℝ, |δ| < η → |x| ≤ 1 →
        |(constantTermSecant
          ((restrictedJacobianMatrix (2*r) 2 (2*(r+1))
            (paperFixedBindingSplitRates m ξ r δ ε w)
            (toCoordinateSpace (chart
              (arbitrarySplitFiniteState (m+1) ξ r δ j)))).charpoly)).eval x -
          (restrictedJacobianMatrix (2*r) 2 (2*(r+1))
            (paperFixedBindingSplitRates m ξ r 0 ε w)
            (toCoordinateSpace (chart
              (arbitrarySplitFiniteState (m+1) ξ r 0 j)))).charpoly.derivative.eval 0| ≤
          C*(|δ|+|x|) := by
  let base (δ : ℝ) := arbitrarySplitFiniteRates (m+1) ξ r δ
  let u (δ : ℝ) := loadedCoordOfState
    (arbitrarySplitFiniteState (m+1) ξ r δ j)
  have hdiff (w : Fin (m+2) → ℝ) (hw : ∀ i, 0 < w i) :
      DifferentiableAt ℝ (fun δ =>
        loadedJacobianMatrix (2*r) 2 (2*(r+1))
          (relaxRates (paperFixedBindingRates
            (edgeScaledRates w (base δ))) ε) (u δ)) 0 := by
    simpa only [base, u, paperFixedBindingSplitRates] using
      paperFixedBindingSplit_loadedJacobian_differentiableAt_full
        m ξ r ε w hr hD₀ hB₀ hbase0 hw j
  have hbasezero : (base 0).Positive := by
    simpa only [base, arbitrarySplitFiniteRates_zero_eq_coalesced]
      using hbase0
  obtain ⟨η, C, hη, hC, hrect⟩ :=
    paperFixedBinding_compact_secant_first_order
      (2*r) 2 (2*(r+1)) ε base u K hK hKpos
      hbasezero hsource hdiff
  refine ⟨η, C, hη, hC, ?_⟩
  intro w hw δ x hδ hx
  have hpoly (s : ℝ) :
      (loadedJacobianMatrix (2*r) 2 (2*(r+1))
        (relaxRates (paperFixedBindingRates
          (edgeScaledRates w (base s))) ε) (u s)).charpoly =
      (restrictedJacobianMatrix (2*r) 2 (2*(r+1))
        (paperFixedBindingSplitRates m ξ r s ε w)
        (toCoordinateSpace (chart
          (arbitrarySplitFiniteState (m+1) ξ r s j)))).charpoly := by
    rw [loadedJacobianMatrix_charpoly_eq_restricted]
    simp only [u, base, paperFixedBindingSplitRates,
      loadedCoordOfState, from_toLoadedCoord]
  simpa only [hpoly δ, hpoly 0, base, u] using
    hrect w hw δ x hδ hx

end

end PhosphorylationStableCapacity
