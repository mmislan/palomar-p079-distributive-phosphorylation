module
public import proofs.PhosphorylationStableCapacity.PaperFixedBindingJointContinuity435
public import proofs.PhosphorylationStableCapacity.CompactNeutralSpectrum435
public import proofs.PhosphorylationStableCapacity.ContinuousNeutralUniformGap435

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section

open PhosphorylationSharpness Polynomial Filter
open scoped Topology

/-- A compact family of the paper's exact fixed-binding coalesced
certificates has one shared split interval on which every prescribed
state has one simple real slow eigenvalue and a stable transverse
spectrum. -/
theorem compact_paperFixedBinding_slowMode_eventually
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
    ∀ᶠ δ : ℝ in 𝓝 0,
      ∀ ω ∈ K, ∃ x : ℝ,
        (restrictedJacobianMatrix (2*r) 2 (2*(r+1))
          (paperFixedBindingSplitRates m ξ r δ ε
            (Fin.lastCases τ ω.val))
          (toCoordinateSpace (chart
            (arbitrarySplitFiniteState (m+1) ξ r δ j)))).charpoly.IsRoot x ∧
        (((restrictedJacobianMatrix (2*r) 2 (2*(r+1))
          (paperFixedBindingSplitRates m ξ r δ ε
            (Fin.lastCases τ ω.val))
          (toCoordinateSpace (chart
            (arbitrarySplitFiniteState (m+1) ξ r δ j)))).map
              (algebraMap ℝ ℂ)).charpoly).derivative.eval (x : ℂ) ≠ 0 ∧
        ∀ z : ℂ,
          z ∈ spectrum ℂ
            ((restrictedJacobianMatrix (2*r) 2 (2*(r+1))
              (paperFixedBindingSplitRates m ξ r δ ε
                (Fin.lastCases τ ω.val))
              (toCoordinateSpace (chart
                (arbitrarySplitFiniteState (m+1) ξ r δ j)))).map
                  (algebraMap ℝ ℂ)) →
            z.re < 0 ∨ z = (x : ℂ) := by
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
  have hzero : ∀ ω ∈ K, SimpleNeutralHurwitzComplement (J (ω, 0)) := by
    intro ω hω
    dsimp only [J]
    rw [paperFixedBindingSplit_restrictedJacobianMatrix_zero_eq_coalesced
      m ξ r ε (Fin.lastCases τ ω.val : Fin (m+2) → ℝ) j]
    exact hspec ω hω
  simpa only [J] using
    compact_jointNeutralMatrix_slowMode_eventually K hK J hJ hzero

/-- The paper's fixed-binding family has a single negative margin for
every nonselected mode throughout a compact current family and one
common split interval. -/
theorem compact_paperFixedBinding_slowMode_uniform_gap
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
    ∃ α : ℝ, 0 < α ∧
      ∀ᶠ δ : ℝ in 𝓝 0,
        ∀ ω ∈ K, ∃ x : ℝ,
          let J := restrictedJacobianMatrix (2*r) 2 (2*(r+1))
            (paperFixedBindingSplitRates m ξ r δ ε
              (Fin.lastCases τ ω.val))
            (toCoordinateSpace (chart
              (arbitrarySplitFiniteState (m+1) ξ r δ j)))
          J.charpoly.IsRoot x ∧
            (((J.map (algebraMap ℝ ℂ)).charpoly).derivative.eval
              (x : ℂ) ≠ 0) ∧
            ∀ z : ℂ, z ∈ spectrum ℂ (J.map (algebraMap ℝ ℂ)) →
              z = (x : ℂ) ∨ z.re ≤ -α := by
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
  have hzero : ∀ ω ∈ K, SimpleNeutralHurwitzComplement (J (ω, 0)) := by
    intro ω hω
    dsimp only [J]
    rw [paperFixedBindingSplit_restrictedJacobianMatrix_zero_eq_coalesced
      m ξ r ε (Fin.lastCases τ ω.val : Fin (m+2) → ℝ) j]
    exact hspec ω hω
  simpa only [J] using
    compact_jointNeutralMatrix_slowMode_uniform_gap K hK J hJ hzero

/-- Finiteness of the prescribed split-root list makes the margin and
the split interval common to every one of its `2m+3` equilibria. -/
theorem compact_paperFixedBinding_all_split_slowMode_uniform_gap
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
          (coalescedFiniteState (m+1) r))))) :
    ∃ α : ℝ, 0 < α ∧
      ∀ᶠ δ : ℝ in 𝓝 0,
        ∀ (j : Fin (2*(m+1)+1)) (ω : PositivePrefixCurrents m),
          ω ∈ K → ∃ x : ℝ,
            let J := restrictedJacobianMatrix (2*r) 2 (2*(r+1))
              (paperFixedBindingSplitRates m ξ r δ ε
                (Fin.lastCases τ ω.val))
              (toCoordinateSpace (chart
                (arbitrarySplitFiniteState (m+1) ξ r δ j)))
            J.charpoly.IsRoot x ∧
              (((J.map (algebraMap ℝ ℂ)).charpoly).derivative.eval
                (x : ℂ) ≠ 0) ∧
              ∀ z : ℂ, z ∈ spectrum ℂ (J.map (algebraMap ℝ ℂ)) →
                z = (x : ℂ) ∨ z.re ≤ -α := by
  classical
  let H (j : Fin (2*(m+1)+1)) :=
    compact_paperFixedBinding_slowMode_uniform_gap
      m ξ r τ ε K hK hr hD₀ hB₀ hbase hspec j
  let a : Fin (2*(m+1)+1) → ℝ := fun j => Classical.choose (H j)
  have ha (j : Fin (2*(m+1)+1)) : 0 < a j :=
    (Classical.choose_spec (H j)).1
  have hevent (j : Fin (2*(m+1)+1)) :
      ∀ᶠ δ : ℝ in 𝓝 0,
        ∀ ω ∈ K, ∃ x : ℝ,
          let J := restrictedJacobianMatrix (2*r) 2 (2*(r+1))
            (paperFixedBindingSplitRates m ξ r δ ε
              (Fin.lastCases τ ω.val))
            (toCoordinateSpace (chart
              (arbitrarySplitFiniteState (m+1) ξ r δ j)))
          J.charpoly.IsRoot x ∧
            (((J.map (algebraMap ℝ ℂ)).charpoly).derivative.eval
              (x : ℂ) ≠ 0) ∧
            ∀ z : ℂ, z ∈ spectrum ℂ (J.map (algebraMap ℝ ℂ)) →
              z = (x : ℂ) ∨ z.re ≤ -(a j) :=
    (Classical.choose_spec (H j)).2
  let s : Finset ℝ := Finset.univ.image a
  have hs : s.Nonempty := by
    refine ⟨a ⟨0, by omega⟩, ?_⟩
    exact Finset.mem_image.mpr ⟨⟨0, by omega⟩,
      Finset.mem_univ _, rfl⟩
  let α : ℝ := s.min' hs
  have hα : 0 < α := by
    have hmem : α ∈ s := Finset.min'_mem s hs
    rcases Finset.mem_image.mp hmem with ⟨j, _, hjval⟩
    have hjα : a j = α := hjval
    exact hjα ▸ ha j
  have hle (j : Fin (2*(m+1)+1)) : α ≤ a j :=
    Finset.min'_le s (a j) (Finset.mem_image.mpr
      ⟨j, Finset.mem_univ _, rfl⟩)
  refine ⟨α, hα, ?_⟩
  have hall : ∀ᶠ δ : ℝ in 𝓝 0,
      ∀ j : Fin (2*(m+1)+1), ∀ ω ∈ K, ∃ x : ℝ,
        let J := restrictedJacobianMatrix (2*r) 2 (2*(r+1))
          (paperFixedBindingSplitRates m ξ r δ ε
            (Fin.lastCases τ ω.val))
          (toCoordinateSpace (chart
            (arbitrarySplitFiniteState (m+1) ξ r δ j)))
        J.charpoly.IsRoot x ∧
          (((J.map (algebraMap ℝ ℂ)).charpoly).derivative.eval
            (x : ℂ) ≠ 0) ∧
          ∀ z : ℂ, z ∈ spectrum ℂ (J.map (algebraMap ℝ ℂ)) →
            z = (x : ℂ) ∨ z.re ≤ -(a j) :=
    Filter.eventually_all.mpr hevent
  filter_upwards [hall] with δ hδ j ω hω
  obtain ⟨x, hx, hsimple, hgap⟩ := hδ j ω hω
  refine ⟨x, hx, hsimple, ?_⟩
  intro z hz
  rcases hgap z hz with hsame | hleft
  · exact Or.inl hsame
  · exact Or.inr (by linarith [hle j])

end

end PhosphorylationStableCapacity
