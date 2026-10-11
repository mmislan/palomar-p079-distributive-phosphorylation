module
public import proofs.PhosphorylationStableCapacity.PaperFixedBindingAnalyticSlowMode
public import proofs.PhosphorylationStableCapacity.SelectedTransverseRootChoice435
public import proofs.PhosphorylationStableCapacity.CompactPaperFixedBindingSplitSpectrum435

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section

open PhosphorylationSharpness Filter Matrix Polynomial
open scoped Topology

/-- The selected root depends only on the matrix at the fixed
parameter, not on the type used to index a matrix family. -/
theorem selectedTransverseRoot_congr_at
    {β γ ι : Type*} [Fintype ι] [DecidableEq ι]
    (J : β → ℝ → Matrix ι ι ℝ)
    (L : γ → ℝ → Matrix ι ι ℝ)
    (α : ℝ) (b : β) (c : γ)
    (h : ∀ δ, J b δ = L c δ) (δ : ℝ) :
    selectedTransverseRoot J α b δ =
      selectedTransverseRoot L α c δ := by
  classical
  simp only [selectedTransverseRoot, h δ]

/-- The root selected by one signed compact transverse certificate is
the analytic root of the literal fixed-binding Jacobian at every
current and split state. The selection is made before the positive
split interval is restricted for the quantitative law. -/
theorem paperFixedBinding_compact_selected_root_analyticAt
    (m : ℕ) (ξ : ℕ → ℝ) (r τ ε : ℝ)
    (K : Set (PositivePrefixCurrents m)) (_hK : IsCompact K)
    (hr : r ≠ 0)
    (hD₀ : DensePositive (coalescedRawD (m+1) r) (m+1))
    (hB₀ : DensePositive (coalescedRawB (m+1) r) (m+1))
    (hbase : ∀ a ∈ K,
      (coalescedAllScaledRates m r
        (Fin.lastCases τ a.val)).Positive)
    (hspec : ∀ a ∈ K, SimpleNeutralHurwitzComplement
      (restrictedJacobianMatrix (2*r) 2 (2*(r+1))
        (relaxRates (paperFixedBindingRates
          (coalescedAllScaledRates m r
            (Fin.lastCases τ a.val))) ε)
        (fromLoadedCoord (loadedCoordOfState
          (coalescedFiniteState (m+1) r)))))
    (α : ℝ) (hα : 0 < α)
    (hgap : ∀ᶠ δ : ℝ in 𝓝 0,
      ∀ (i : Fin (2*(m+1)+1)) (a : PositivePrefixCurrents m),
        a ∈ K → ∃ lam : ℝ,
          let J := restrictedJacobianMatrix (2*r) 2 (2*(r+1))
            (paperFixedBindingSplitRates m ξ r δ ε
              (Fin.lastCases τ a.val))
            (toCoordinateSpace (chart
              (arbitrarySplitFiniteState (m+1) ξ r δ i)))
          J.charpoly.IsRoot lam ∧
            ((J.map (algebraMap ℝ ℂ)).charpoly).derivative.eval
              (lam : ℂ) ≠ 0 ∧
            ∀ z : ℂ, z ∈ spectrum ℂ (J.map (algebraMap ℝ ℂ)) →
              z = (lam : ℂ) ∨ z.re ≤ -α) :
      (∀ᶠ δ : ℝ in 𝓝 (0 : ℝ),
        ∀ (j : Fin (2*(m+1)+1)) (a : PositivePrefixCurrents m),
          a ∈ K →
            SimpleTransverseRoot
              (restrictedJacobianMatrix (2*r) 2 (2*(r+1))
                (paperFixedBindingSplitRates m ξ r δ ε
                  (Fin.lastCases τ a.val))
                (toCoordinateSpace (chart
                  (arbitrarySplitFiniteState (m+1) ξ r δ j))))
              α
              (selectedTransverseRoot
                (fun (p : PositivePrefixCurrents m) (s : ℝ) =>
                  restrictedJacobianMatrix (2*r) 2 (2*(r+1))
                    (paperFixedBindingSplitRates m ξ r s ε
                      (Fin.lastCases τ p.val))
                    (toCoordinateSpace (chart
                      (arbitrarySplitFiniteState (m+1) ξ r s j))))
                α a δ)) ∧
      (∀ (j : Fin (2*(m+1)+1)) (a : PositivePrefixCurrents m),
        a ∈ K →
          let J := fun (p : PositivePrefixCurrents m) (s : ℝ) =>
            restrictedJacobianMatrix (2*r) 2 (2*(r+1))
              (paperFixedBindingSplitRates m ξ r s ε
                (Fin.lastCases τ p.val))
              (toCoordinateSpace (chart
                (arbitrarySplitFiniteState (m+1) ξ r s j)))
          AnalyticAt ℝ (selectedTransverseRoot J α a) 0 ∧
            selectedTransverseRoot J α a 0 = 0) := by
  refine ⟨?_, ?_⟩
  · filter_upwards [hgap] with δ hd j a ha
    let J := fun (p : PositivePrefixCurrents m) (s : ℝ) =>
      restrictedJacobianMatrix (2*r) 2 (2*(r+1))
        (paperFixedBindingSplitRates m ξ r s ε
          (Fin.lastCases τ p.val))
        (toCoordinateSpace (chart
          (arbitrarySplitFiniteState (m+1) ξ r s j)))
    have hcert : ∃ x : ℝ, SimpleTransverseRoot (J a δ) α x := by
      simpa only [J, SimpleTransverseRoot] using hd j a ha
    exact selectedTransverseRoot_spec J α a δ hcert
  · intro j a ha
    let J := fun (p : PositivePrefixCurrents m) (s : ℝ) =>
      restrictedJacobianMatrix (2*r) 2 (2*(r+1))
        (paperFixedBindingSplitRates m ξ r s ε
          (Fin.lastCases τ p.val))
        (toCoordinateSpace (chart
          (arbitrarySplitFiniteState (m+1) ξ r s j)))
    obtain ⟨branch, hbranch, hbranch0, hroot⟩ :=
      paperFixedBinding_analytic_slow_branch m ξ r τ ε a.val
        hr hD₀ hB₀ (hbase a ha) (hspec a ha) j
    have hnear : ∀ᶠ δ : ℝ in 𝓝 (0 : ℝ), -α < branch δ :=
      hbranch.continuousAt.eventually
        (Ioi_mem_nhds (by rw [hbranch0]; linarith : -α < branch 0))
    have heq : branch =ᶠ[𝓝 (0 : ℝ)]
        selectedTransverseRoot J α a := by
      filter_upwards [hgap, hroot, hnear]
        with δ hgapδ hrootδ hnearδ
      have hcert : ∃ x : ℝ, SimpleTransverseRoot (J a δ) α x := by
        simpa only [J, SimpleTransverseRoot] using hgapδ j a ha
      exact near_root_eq_selectedTransverseRoot J α a δ
        (branch δ) hcert (by simpa only [J] using hrootδ) hnearδ
    exact ⟨hbranch.congr heq, by rw [← heq.eq_of_nhds, hbranch0]⟩

end

end PhosphorylationStableCapacity
