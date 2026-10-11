module
public import proofs.PhosphorylationStableCapacity.PaperFixedBindingJointContinuity435
public import proofs.PhosphorylationStableCapacity.SimpleNeutralPositiveCoefficient435
public import proofs.PhosphorylationStableCapacity.PaperFixedBindingCoalescence435

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section

open PhosphorylationSharpness Matrix Polynomial
open scoped Topology

/-- The literal fixed-binding coalesced transverse characteristic
coefficient has one positive lower bound on a compact prefix-current
family; the bound belongs to the same matrices used after splitting. -/
theorem paperFixedBinding_compact_coalesced_coeff_one_lower
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
    (j : Fin (2*(m+1)+1)) :
    ∃ pmin : ℝ, 0 < pmin ∧
      ∀ ω ∈ K, pmin ≤
        (restrictedJacobianMatrix (2*r) 2 (2*(r+1))
          (paperFixedBindingSplitRates m ξ r 0 ε
            (Fin.lastCases τ ω.val))
          (toCoordinateSpace (chart
            (arbitrarySplitFiniteState (m+1) ξ r 0 j)))).charpoly.derivative.eval 0 := by
  let J (ω : PositivePrefixCurrents m) :=
    restrictedJacobianMatrix (2*r) 2 (2*(r+1))
      (paperFixedBindingSplitRates m ξ r 0 ε
        (Fin.lastCases τ ω.val))
      (toCoordinateSpace (chart
        (arbitrarySplitFiniteState (m+1) ξ r 0 j)))
  have hJ : ContinuousOn J K := by
    intro ω hω
    let F : PositivePrefixCurrents m × ℝ →
        Matrix (Fin (m+2) ⊕ (Fin (m+2) ⊕ Fin (m+2)))
          (Fin (m+2) ⊕ (Fin (m+2) ⊕ Fin (m+2))) ℝ :=
      fun p => restrictedJacobianMatrix (2*r) 2 (2*(r+1))
        (paperFixedBindingSplitRates m ξ r p.2 ε
          (Fin.lastCases τ p.1.val))
        (toCoordinateSpace (chart
          (arbitrarySplitFiniteState (m+1) ξ r p.2 j)))
    have hF : ContinuousAt F (ω, 0) :=
      paperFixedBindingSplit_restrictedJacobianMatrix_joint_continuousAt
      m ξ r τ ε ω hr hD₀ hB₀ (hbase ω hω) j
    have hpair : ContinuousAt
        (fun a : PositivePrefixCurrents m => (a, (0 : ℝ))) ω := by
      fun_prop
    simpa only [J, F, Function.comp_def] using
      (hF.comp (f := fun a : PositivePrefixCurrents m => (a, (0 : ℝ)))
        (g := F) (x := ω) hpair).continuousWithinAt
  have hneutral : ∀ ω ∈ K, SimpleNeutralHurwitzComplement (J ω) := by
    intro ω hω
    dsimp only [J]
    rw [paperFixedBindingSplit_restrictedJacobianMatrix_zero_eq_coalesced]
    exact hspec ω hω
  obtain ⟨pmin, hpmin, hbound⟩ :=
    compact_simpleNeutral_charpoly_coeff_one_lower K hK J hJ hneutral
  refine ⟨pmin, hpmin, ?_⟩
  intro ω hω
  have hcoeff : (J ω).charpoly.derivative.eval 0 =
      (J ω).charpoly.coeff 1 := by
    rw [← Polynomial.coeff_zero_eq_eval_zero,
      Polynomial.coeff_derivative]
    norm_num
  change pmin ≤ (J ω).charpoly.derivative.eval 0
  rw [hcoeff]
  exact hbound ω hω

end

end PhosphorylationStableCapacity
