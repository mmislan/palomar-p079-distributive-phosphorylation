module
public import proofs.PhosphorylationStableCapacity.PaperFixedBindingJacobianAnalytic
public import proofs.PhosphorylationStableCapacity.PaperFixedBindingCoalescence435
public import proofs.PhosphorylationStableCapacity.AnalyticPolynomialSlowBranch
public import proofs.PhosphorylationStableCapacity.SimpleNeutralPositiveCoefficient435

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section

open PhosphorylationSharpness Filter Polynomial Matrix
open scoped Topology

/-- The simple zero characteristic root of the genuine manuscript
fixed-binding family has a real-analytic branch at coalescence. -/
theorem paperFixedBinding_analytic_slow_branch
    (m : ℕ) (ξ : ℕ → ℝ)
    (r τ ε : ℝ) (ω : Fin (m+1) → ℝ) (hr : r ≠ 0)
    (hD₀ : DensePositive (coalescedRawD (m+1) r) (m+1))
    (hB₀ : DensePositive (coalescedRawB (m+1) r) (m+1))
    (hbase : (coalescedAllScaledRates m r
      (Fin.lastCases τ ω)).Positive)
    (hspec : SimpleNeutralHurwitzComplement
      (restrictedJacobianMatrix (2*r) 2 (2*(r+1))
        (relaxRates (paperFixedBindingRates
          (coalescedAllScaledRates m r (Fin.lastCases τ ω))) ε)
        (fromLoadedCoord (loadedCoordOfState
          (coalescedFiniteState (m+1) r)))))
    (j : Fin (2*(m+1)+1)) :
    ∃ lam : ℝ → ℝ,
      AnalyticAt ℝ lam 0 ∧ lam 0 = 0 ∧
      ∀ᶠ δ : ℝ in 𝓝 (0 : ℝ),
        (restrictedJacobianMatrix (2*r) 2 (2*(r+1))
          (paperFixedBindingSplitRates m ξ r δ ε
            (Fin.lastCases τ ω))
          (toCoordinateSpace (chart
            (arbitrarySplitFiniteState (m+1) ξ r δ j)))).charpoly.IsRoot
          (lam δ) := by
  let J : ℝ → Matrix (Fin (m+2) ⊕ (Fin (m+2) ⊕ Fin (m+2)))
      (Fin (m+2) ⊕ (Fin (m+2) ⊕ Fin (m+2))) ℝ := fun δ =>
    restrictedJacobianMatrix (2*r) 2 (2*(r+1))
      (paperFixedBindingSplitRates m ξ r δ ε
        (Fin.lastCases τ ω))
      (toCoordinateSpace (chart
        (arbitrarySplitFiniteState (m+1) ξ r δ j)))
  let P : ℝ → ℝ[X] := fun δ => (J δ).charpoly
  have hcard : Fintype.card
      (Fin (m+2) ⊕ (Fin (m+2) ⊕ Fin (m+2))) = 3*(m+2) := by
    simp [Fintype.card_sum, Fintype.card_fin]; omega
  have hdegree (δ : ℝ) : (P δ).natDegree < 3*(m+2)+1 := by
    change (J δ).charpoly.natDegree < 3*(m+2)+1
    rw [(J δ).charpoly_natDegree_eq_dim, hcard]
    omega
  have hcoeff (q : ℕ) :
      AnalyticAt ℝ (fun δ => (P δ).coeff q) 0 :=
    paperFixedBindingSplit_charpoly_coeff_analyticAt
      m ξ r τ ε ω hr hD₀ hB₀ hbase j q
  have hJzero : J 0 =
      restrictedJacobianMatrix (2*r) 2 (2*(r+1))
        (relaxRates (paperFixedBindingRates
          (coalescedAllScaledRates m r (Fin.lastCases τ ω))) ε)
        (fromLoadedCoord (loadedCoordOfState
          (coalescedFiniteState (m+1) r))) := by
    simpa only [J] using
      paperFixedBindingSplit_restrictedJacobianMatrix_zero_eq_coalesced
        m ξ r ε (Fin.lastCases τ ω) j
  have hzero : (P 0).eval 0 = 0 := by
    change (J 0).charpoly.eval 0 = 0
    rw [hJzero]
    obtain ⟨q, hfactor, _, _⟩ := hspec
    have hcomplex :
        ((restrictedJacobianMatrix (2*r) 2 (2*(r+1))
          (relaxRates (paperFixedBindingRates
            (coalescedAllScaledRates m r (Fin.lastCases τ ω))) ε)
          (fromLoadedCoord (loadedCoordOfState
            (coalescedFiniteState (m+1) r)))).map
              (algebraMap ℝ ℂ)).charpoly.eval 0 = 0 := by
      rw [hfactor]
      simp
    have hreal :
        (((restrictedJacobianMatrix (2*r) 2 (2*(r+1))
          (relaxRates (paperFixedBindingRates
            (coalescedAllScaledRates m r (Fin.lastCases τ ω))) ε)
          (fromLoadedCoord (loadedCoordOfState
            (coalescedFiniteState (m+1) r)))).charpoly.eval 0 : ℝ) : ℂ) = 0 := by
      rw [Matrix.charpoly_map] at hcomplex
      simpa only [← Polynomial.coeff_zero_eq_eval_zero,
        Polynomial.coeff_map, Complex.coe_algebraMap] using hcomplex
    exact_mod_cast hreal
  have hpivot : (P 0).derivative.eval 0 ≠ 0 := by
    have hp := simpleNeutral_real_charpoly_coeff_one_pos _ hspec
    change (J 0).charpoly.derivative.eval 0 ≠ 0
    rw [hJzero, ← Polynomial.coeff_zero_eq_eval_zero,
      Polynomial.coeff_derivative]
    simpa using ne_of_gt hp
  obtain ⟨lam, hlam, hlam0, hroot⟩ :=
    analytic_simple_polynomial_zero_branch P (3*(m+2)+1)
      hdegree hcoeff hzero hpivot
  exact ⟨lam, hlam, hlam0,
    hroot.mono (by intro δ hδ; exact hδ)⟩

end
end PhosphorylationStableCapacity
