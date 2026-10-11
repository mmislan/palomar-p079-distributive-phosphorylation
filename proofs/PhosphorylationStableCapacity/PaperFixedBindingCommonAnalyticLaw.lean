module
public import proofs.PhosphorylationStableCapacity.PaperFixedBindingQuantitativeAnalyticFamily

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section

open PhosphorylationSharpness Filter Polynomial
open scoped Topology

/-- One literal paper rate vector has analytic selected slow branches for
every arbitrary ordered offset, a common printed coefficient, a common
relative-error bound, and a common transverse spectral margin. -/
theorem paperFixedBinding_all_indices_common_analytic_printed_law
    (m : ℕ) (ξ : ℕ → ℝ) (hξ : StrictMono ξ)
    (r τ ε : ℝ) (ω : Fin (m+1) → ℝ)
    (hω : ∀ i, 0 < ω i)
    (hr : 1 < r) (hτ : 0 < τ) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hD₀ : DensePositive (coalescedRawD (m+1) r) (m+1))
    (hB₀ : DensePositive (coalescedRawB (m+1) r) (m+1))
    (hbase : (coalescedAllScaledRates m r
      (Fin.lastCases τ ω)).Positive)
    (hk₀ : (relaxRates (paperFixedBindingRates
      (coalescedAllScaledRates m r (Fin.lastCases τ ω))) ε).Positive)
    (hx₀ : (coalescedFiniteState (m+1) r).Positive)
    (heq₀ : Equilibrium
      (relaxRates (paperFixedBindingRates
        (coalescedAllScaledRates m r (Fin.lastCases τ ω))) ε)
      (coalescedFiniteState (m+1) r))
    (hET₀ : totalE (coalescedFiniteState (m+1) r) = 2*r)
    (hFT₀ : totalF (coalescedFiniteState (m+1) r) = 2)
    (hspec : SimpleNeutralHurwitzComplement
      (restrictedJacobianMatrix (2*r) 2 (2*(r+1))
        (relaxRates (paperFixedBindingRates
          (coalescedAllScaledRates m r (Fin.lastCases τ ω))) ε)
        (fromLoadedCoord (loadedCoordOfState
          (coalescedFiniteState (m+1) r))))) :
    ∃ lam : Fin (2*(m+1)+1) → ℝ → ℝ,
      (∀ j, AnalyticAt ℝ (lam j) 0 ∧ lam j 0 = 0) ∧
      0 < paperFixedBindingPrintedCoefficient m r τ ε ω ∧
      ∃ α K : ℝ, 0 < α ∧ 0 < K ∧
        ∀ᶠ δ : ℝ in 𝓝[>] (0 : ℝ),
          ∀ j : Fin (2*(m+1)+1),
            let J := restrictedJacobianMatrix (2*r) 2 (2*(r+1))
              (paperFixedBindingSplitRates m ξ r δ ε
                (Fin.lastCases τ ω))
              (toCoordinateSpace (chart
                (arbitrarySplitFiniteState (m+1) ξ r δ j)))
            J.charpoly.IsRoot (lam j δ) ∧
            ((J.map (algebraMap ℝ ℂ)).charpoly).derivative.eval
              ((lam j δ) : ℂ) ≠ 0 ∧
            (∀ z : ℂ, z ∈ spectrum ℂ (J.map (algebraMap ℝ ℂ)) →
              z = ((lam j δ) : ℂ) ∨ z.re ≤ -α) ∧
            |lam j δ / (-paperFixedBindingPrintedCoefficient
                m r τ ε ω * δ^(2*(m+1)) *
                (∏ i ∈ (Finset.range (2*(m+1)+1)).erase j.val,
                  (ξ j.val-ξ i))) - 1| ≤ K*|δ| := by
  classical
  have ha : 0 < paperFixedBindingPrintedCoefficient m r τ ε ω :=
    paperFixedBindingPrintedCoefficient_pos
      m ξ r τ ε ω 0 hr hD₀ hk₀ hx₀ heq₀ hET₀ hFT₀ hspec
  have hper (j : Fin (2*(m+1)+1)) :=
    paperFixedBinding_quantitative_analytic_slow_mode_family
      m ξ hξ r τ ε ω hω hr hτ hε hε1 hD₀ hB₀
      hbase hk₀ hx₀ heq₀ hET₀ hFT₀ hspec j
  choose lam hlam hlam0 α K hα hK hEv using hper
  let A : Finset ℝ := Finset.univ.image α
  have hA : A.Nonempty := by
    refine ⟨α 0, ?_⟩
    exact Finset.mem_image.mpr ⟨0, Finset.mem_univ _, rfl⟩
  let αall : ℝ := A.min' hA
  have hαall : 0 < αall := by
    have hmem := A.min'_mem hA
    obtain ⟨j, _, hj⟩ := Finset.mem_image.mp hmem
    dsimp [αall]
    rw [← hj]
    exact hα j
  have hαbound (j : Fin (2*(m+1)+1)) : αall ≤ α j :=
    Finset.min'_le A (α j) (Finset.mem_image.mpr
      ⟨j, Finset.mem_univ _, rfl⟩)
  let Kall : ℝ := ∑ j : Fin (2*(m+1)+1), K j
  have hKbound (j : Fin (2*(m+1)+1)) : K j ≤ Kall :=
    Finset.single_le_sum (fun i hi => (hK i).le) (Finset.mem_univ j)
  have hKall : 0 < Kall := lt_of_lt_of_le (hK 0) (hKbound 0)
  refine ⟨lam, (fun j => ⟨hlam j, hlam0 j⟩), ha,
    αall, Kall, hαall, hKall, ?_⟩
  have hEvAll := Filter.eventually_all.mpr hEv
  filter_upwards [hEvAll] with δ hδ j
  obtain ⟨hroot, hsimple, hstable, hbound⟩ := hδ j
  have hstable' : ∀ z : ℂ,
      z ∈ spectrum ℂ
        ((restrictedJacobianMatrix (2*r) 2 (2*(r+1))
          (paperFixedBindingSplitRates m ξ r δ ε
            (Fin.lastCases τ ω))
          (toCoordinateSpace (chart
            (arbitrarySplitFiniteState (m+1) ξ r δ j)))).map
              (algebraMap ℝ ℂ)) →
      z = ((lam j δ) : ℂ) ∨ z.re ≤ -αall := by
    intro z hz
    rcases hstable z hz with heq | hneg
    · exact Or.inl heq
    · exact Or.inr (by have hle := hαbound j; linarith)
  exact ⟨hroot, hsimple, hstable',
    hbound.trans
      (mul_le_mul_of_nonneg_right (hKbound j) (abs_nonneg δ))⟩

end
end PhosphorylationStableCapacity
