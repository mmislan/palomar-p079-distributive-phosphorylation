module
public import proofs.PhosphorylationStableCapacity.CompactPaperFixedBindingSplitSpectrum435
public import proofs.PhosphorylationStableCapacity.CompactNeutralSmallRoot435

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section

open PhosphorylationSharpness Filter Matrix Polynomial
open scoped Topology

/-- The exact same simple transverse slow root selected by the common
compact spectral-gap certificate converges to zero uniformly for all
currents and all split states. This holds on a signed interval, which
also supports the analytic branch-identification step. -/
theorem paperFixedBinding_compact_selected_root_small
    (m : ℕ) (ξ : ℕ → ℝ) (r τ ε : ℝ)
    (K : Set (PositivePrefixCurrents m)) (hK : IsCompact K)
    (hr : r ≠ 0)
    (hD₀ : DensePositive (coalescedRawD (m+1) r) (m+1))
    (hB₀ : DensePositive (coalescedRawB (m+1) r) (m+1))
    (hbase : ∀ ω ∈ K,
      (coalescedAllScaledRates m r
        (Fin.lastCases τ ω.val)).Positive)
    (hspec : ∀ ω ∈ K, SimpleNeutralHurwitzComplement
      (restrictedJacobianMatrix (2*r) 2 (2*(r+1))
        (relaxRates (paperFixedBindingRates
          (coalescedAllScaledRates m r
            (Fin.lastCases τ ω.val))) ε)
        (fromLoadedCoord (loadedCoordOfState
          (coalescedFiniteState (m+1) r)))))
    (α : ℝ) (hα : 0 < α)
    (hgap : ∀ᶠ δ : ℝ in 𝓝 0,
      ∀ (j : Fin (2*(m+1)+1)) (ω : PositivePrefixCurrents m),
        ω ∈ K → ∃ lam : ℝ,
          let J := restrictedJacobianMatrix (2*r) 2 (2*(r+1))
            (paperFixedBindingSplitRates m ξ r δ ε
              (Fin.lastCases τ ω.val))
            (toCoordinateSpace (chart
              (arbitrarySplitFiniteState (m+1) ξ r δ j)))
          J.charpoly.IsRoot lam ∧
            (((J.map (algebraMap ℝ ℂ)).charpoly).derivative.eval
              (lam : ℂ) ≠ 0) ∧
            ∀ z : ℂ, z ∈ spectrum ℂ (J.map (algebraMap ℝ ℂ)) →
              z = (lam : ℂ) ∨ z.re ≤ -α)
    (ρ : ℝ) (hρ : 0 < ρ) :
    ∀ᶠ δ : ℝ in 𝓝 0,
      ∀ (j : Fin (2*(m+1)+1)) (ω : PositivePrefixCurrents m),
        ω ∈ K → ∃ lam : ℝ,
          let J := restrictedJacobianMatrix (2*r) 2 (2*(r+1))
            (paperFixedBindingSplitRates m ξ r δ ε
              (Fin.lastCases τ ω.val))
            (toCoordinateSpace (chart
              (arbitrarySplitFiniteState (m+1) ξ r δ j)))
          |lam| < ρ ∧ J.charpoly.IsRoot lam ∧
            (((J.map (algebraMap ℝ ℂ)).charpoly).derivative.eval
              (lam : ℂ) ≠ 0) ∧
            ∀ z : ℂ, z ∈ spectrum ℂ (J.map (algebraMap ℝ ℂ)) →
              z = (lam : ℂ) ∨ z.re ≤ -α := by
  classical
  have hper (j : Fin (2*(m+1)+1)) :
      ∀ᶠ δ : ℝ in 𝓝 0,
        ∀ ω ∈ K, ∃ lam : ℝ,
          let J := restrictedJacobianMatrix (2*r) 2 (2*(r+1))
            (paperFixedBindingSplitRates m ξ r δ ε
              (Fin.lastCases τ ω.val))
            (toCoordinateSpace (chart
              (arbitrarySplitFiniteState (m+1) ξ r δ j)))
          |lam| < ρ ∧ J.charpoly.IsRoot lam ∧
            (((J.map (algebraMap ℝ ℂ)).charpoly).derivative.eval
              (lam : ℂ) ≠ 0) ∧
            ∀ z : ℂ, z ∈ spectrum ℂ (J.map (algebraMap ℝ ℂ)) →
              z = (lam : ℂ) ∨ z.re ≤ -α := by
    let J : PositivePrefixCurrents m × ℝ →
        Matrix (Fin (m+2) ⊕ (Fin (m+2) ⊕ Fin (m+2)))
          (Fin (m+2) ⊕ (Fin (m+2) ⊕ Fin (m+2))) ℝ :=
      fun p => restrictedJacobianMatrix (2*r) 2 (2*(r+1))
        (paperFixedBindingSplitRates m ξ r p.2 ε
          (Fin.lastCases τ p.1.val))
        (toCoordinateSpace (chart
          (arbitrarySplitFiniteState (m+1) ξ r p.2 j)))
    have hJ : ∀ ω ∈ K, ContinuousAt J (ω, 0) := by
      intro ω hω
      dsimp only [J]
      exact paperFixedBindingSplit_restrictedJacobianMatrix_joint_continuousAt
        m ξ r τ ε ω hr hD₀ hB₀ (hbase ω hω) j
    have hzero : ∀ ω ∈ K,
        SimpleNeutralHurwitzComplement (J (ω, 0)) := by
      intro ω hω
      dsimp only [J]
      rw [paperFixedBindingSplit_restrictedJacobianMatrix_zero_eq_coalesced
        m ξ r ε (Fin.lastCases τ ω.val : Fin (m+2) → ℝ) j]
      exact hspec ω hω
    have hgapj : ∀ᶠ δ : ℝ in 𝓝 0,
        ∀ ω ∈ K, ∃ lam : ℝ,
          (J (ω, δ)).charpoly.IsRoot lam ∧
          (((J (ω, δ)).map (algebraMap ℝ ℂ)).charpoly).derivative.eval
            (lam : ℂ) ≠ 0 ∧
          ∀ z : ℂ,
            z ∈ spectrum ℂ ((J (ω, δ)).map (algebraMap ℝ ℂ)) →
              z = (lam : ℂ) ∨ z.re ≤ -α := by
      filter_upwards [hgap] with δ hd ω hw
      simpa only [J] using hd j ω hw
    simpa only [J] using
      compact_jointNeutralMatrix_selected_root_small
        K hK J hJ hzero α hα hgapj ρ hρ
  exact Filter.eventually_all.mpr hper

end

end PhosphorylationStableCapacity
