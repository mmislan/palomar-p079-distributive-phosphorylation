module
public import proofs.PhosphorylationStableCapacity.PaperFixedBindingAnalyticSlowMode
public import proofs.PhosphorylationStableCapacity.PaperFixedBindingQuantitativeFamily
public import proofs.PhosphorylationStableCapacity.AnalyticSlowModeIdentification

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section

open PhosphorylationSharpness Filter Polynomial
open scoped Topology

/-- The analytic branch of the literal fixed-binding family is exactly
the selected simple quantitative slow mode, with one transverse margin. -/
theorem paperFixedBinding_quantitative_analytic_slow_mode_family
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
          (coalescedFiniteState (m+1) r)))))
    (j : Fin (2*(m+1)+1)) :
    ∃ lam : ℝ → ℝ, AnalyticAt ℝ lam 0 ∧ lam 0 = 0 ∧
      ∃ α K : ℝ, 0 < α ∧ 0 < K ∧
        ∀ᶠ δ : ℝ in 𝓝[>] (0 : ℝ),
          let J := restrictedJacobianMatrix (2*r) 2 (2*(r+1))
            (paperFixedBindingSplitRates m ξ r δ ε
              (Fin.lastCases τ ω))
            (toCoordinateSpace (chart
              (arbitrarySplitFiniteState (m+1) ξ r δ j)))
          J.charpoly.IsRoot (lam δ) ∧
          ((J.map (algebraMap ℝ ℂ)).charpoly).derivative.eval
            ((lam δ) : ℂ) ≠ 0 ∧
          (∀ z : ℂ, z ∈ spectrum ℂ (J.map (algebraMap ℝ ℂ)) →
            z = ((lam δ) : ℂ) ∨ z.re ≤ -α) ∧
          |lam δ / (-paperFixedBindingPrintedCoefficient m r τ ε ω *
              δ^(2*(m+1)) *
              (∏ i ∈ (Finset.range (2*(m+1)+1)).erase j.val,
                (ξ j.val-ξ i))) - 1| ≤ K*|δ| := by
  obtain ⟨lam, hlam, hlam0, hrootAnalytic⟩ :=
    paperFixedBinding_analytic_slow_branch
      m ξ r τ ε ω (ne_of_gt (lt_trans zero_lt_one hr))
      hD₀ hB₀ hbase hspec j
  obtain ⟨α, K, hα, hK, hquant⟩ :=
    paperFixedBinding_quantitative_slow_mode_family
      m ξ hξ r τ ε ω hω hr hτ hε hε1 hD₀ hB₀
      hbase hk₀ hx₀ heq₀ hET₀ hFT₀ hspec j
  have hnear : ∀ᶠ δ : ℝ in 𝓝 (0 : ℝ), -α < lam δ := by
    have hzero : -α < lam 0 := by rw [hlam0]; linarith
    exact hlam.continuousAt.eventually (Ioi_mem_nhds hzero)
  refine ⟨lam, hlam, hlam0, α, K, hα, hK, ?_⟩
  filter_upwards [hrootAnalytic.filter_mono nhdsWithin_le_nhds,
    hnear.filter_mono nhdsWithin_le_nhds, hquant]
    with δ hroot hnear hquant
  obtain ⟨mu, hmu, hsimple, hmargin, hbound⟩ := hquant
  let J := restrictedJacobianMatrix (2*r) 2 (2*(r+1))
    (paperFixedBindingSplitRates m ξ r δ ε
      (Fin.lastCases τ ω))
    (toCoordinateSpace (chart
      (arbitrarySplitFiniteState (m+1) ξ r δ j)))
  have heq : lam δ = mu :=
    near_real_root_eq_selected_transverse_mode J α mu (lam δ)
      hnear hroot hmargin
  subst mu
  exact ⟨hmu, hsimple, hmargin, hbound⟩

end
end PhosphorylationStableCapacity
