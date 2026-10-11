module
public import proofs.PhosphorylationStableCapacity.PaperFixedBindingCompactPhysicalPrefactor435
public import proofs.PhosphorylationStableCapacity.PaperFixedBindingCompactSecantActual435

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section

open PhosphorylationSharpness Filter Matrix Polynomial
open scoped Topology

/-- The two actual-network uniform estimates needed for the printed
relative slow-eigenvalue law share one compact current family, split
state, fixed-binding rates, and signed split-parameter interval. -/
theorem paperFixedBinding_compact_actual_quantitative_core
    (m : ℕ) (ξ : ℕ → ℝ) (r ε : ℝ)
    (K : Set (Fin (m+2) → ℝ)) (hK : IsCompact K)
    (hKpos : ∀ w ∈ K, ∀ i, 0 < w i)
    (hr : 1 < r) (hε : 0 < ε)
    (hD₀ : DensePositive (coalescedRawD (m+1) r) (m+1))
    (hB₀ : DensePositive (coalescedRawB (m+1) r) (m+1))
    (hbase0 : (coalescedFiniteRates (m+1) r).Positive)
    (hsource : ∀ᶠ δ : ℝ in 𝓝 0,
      (arbitrarySplitFiniteRates (m+1) ξ r δ).Positive)
    (j : Fin (2*(m+1)+1))
    (hstate0 :
      (arbitrarySplitFiniteState (m+1) ξ r 0 j).S 0 *
      (arbitrarySplitFiniteState (m+1) ξ r 0 j).E *
      (arbitrarySplitFiniteState (m+1) ξ r 0 j).F ≠ 0) :
    ∃ A η C : ℝ, 0 < A ∧ 0 < η ∧ 0 < C ∧
      (∀ᶠ δ : ℝ in 𝓝 0,
        ∀ w ∈ K,
          |arbitrarySplitGenericPhysicalPrefactor m ξ r δ
              (paperFixedBindingSplitRates m ξ r δ ε w) j -
            arbitrarySplitGenericPhysicalPrefactor m ξ r 0
              (paperFixedBindingSplitRates m ξ r 0 ε w) j| ≤
                A*|δ|) ∧
      (∀ w ∈ K, ∀ δ x : ℝ, |δ| < η → |x| ≤ 1 →
        |(constantTermSecant
          ((restrictedJacobianMatrix (2*r) 2 (2*(r+1))
            (paperFixedBindingSplitRates m ξ r δ ε w)
            (toCoordinateSpace (chart
              (arbitrarySplitFiniteState (m+1) ξ r δ j)))).charpoly)).eval x -
          (restrictedJacobianMatrix (2*r) 2 (2*(r+1))
            (paperFixedBindingSplitRates m ξ r 0 ε w)
            (toCoordinateSpace (chart
              (arbitrarySplitFiniteState (m+1) ξ r 0 j)))).charpoly.derivative.eval 0| ≤
          C*(|δ|+|x|)) := by
  have hbase :
      (arbitrarySplitFiniteRates (m+1) ξ r 0).Positive := by
    simpa only [arbitrarySplitFiniteRates_zero_eq_coalesced] using hbase0
  obtain ⟨A, hA, hnum⟩ :=
    paperFixedBinding_compact_physicalPrefactor_first_order
      m ξ r ε K hK hKpos hr hε hD₀ hB₀
      hbase hsource j hstate0
  obtain ⟨η, C, hη, hC, hrect⟩ :=
    paperFixedBinding_compact_actual_secant_first_order
      m ξ r ε K hK hKpos (by linarith : r ≠ 0)
      hD₀ hB₀ hbase0 hsource j
  exact ⟨A, η, C, hA, hη, hC, hnum, hrect⟩

end

end PhosphorylationStableCapacity
