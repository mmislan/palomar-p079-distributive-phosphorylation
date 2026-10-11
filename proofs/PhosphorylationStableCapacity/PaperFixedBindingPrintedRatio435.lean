module
public import proofs.PhosphorylationStableCapacity.PaperFixedBindingPrintedCoefficient
public import proofs.PhosphorylationStableCapacity.PaperFixedBindingCoalescence435

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section

open PhosphorylationSharpness Polynomial

/-- The coefficient in the compact actual-matrix relative law is
literally the manuscript's normalized physical coefficient, with the
same coalesced fixed-binding rate vector and the product of nonzero
transverse eigenvalues. -/
theorem paperFixedBindingSplit_zero_physical_ratio_eq_printed
    (m : ℕ) (ξ : ℕ → ℝ) (r τ ε : ℝ)
    (ω : Fin (m+1) → ℝ) (j : Fin (2*(m+1)+1))
    (hr : 1 < r)
    (hD₀ : DensePositive (coalescedRawD (m+1) r) (m+1))
    (hk : (relaxRates (paperFixedBindingRates
      (coalescedAllScaledRates m r (Fin.lastCases τ ω))) ε).Positive)
    (hx : (coalescedFiniteState (m+1) r).Positive)
    (heq : Equilibrium
      (relaxRates (paperFixedBindingRates
        (coalescedAllScaledRates m r (Fin.lastCases τ ω))) ε)
      (coalescedFiniteState (m+1) r))
    (hET : totalE (coalescedFiniteState (m+1) r) = 2*r)
    (hFT : totalF (coalescedFiniteState (m+1) r) = 2) :
    arbitrarySplitGenericPhysicalPrefactor m ξ r 0
        (paperFixedBindingSplitRates m ξ r 0 ε
          (Fin.lastCases τ ω)) j /
      (restrictedJacobianMatrix (2*r) 2 (2*(r+1))
        (paperFixedBindingSplitRates m ξ r 0 ε
          (Fin.lastCases τ ω))
        (toCoordinateSpace (chart
          (arbitrarySplitFiniteState (m+1) ξ r 0 j)))).charpoly.derivative.eval 0 =
      paperFixedBindingPrintedCoefficient m r τ ε ω := by
  let J₀ := restrictedJacobianMatrix (2*r) 2 (2*(r+1))
    (paperFixedBindingSplitRates m ξ r 0 ε
      (Fin.lastCases τ ω))
    (toCoordinateSpace (chart
      (arbitrarySplitFiniteState (m+1) ξ r 0 j)))
  have hJzero :=
    paperFixedBindingSplit_restrictedJacobianMatrix_zero_eq_coalesced
      m ξ r ε (Fin.lastCases τ ω) j
  have hder : J₀.charpoly.derivative.eval 0 =
      (restrictedJacobianMatrix (2*r) 2 (2*(r+1))
        (relaxRates (paperFixedBindingRates
          (coalescedAllScaledRates m r (Fin.lastCases τ ω))) ε)
        (fromLoadedCoord (loadedCoordOfState
          (coalescedFiniteState (m+1) r)))).charpoly.coeff 1 := by
    dsimp only [J₀]
    rw [hJzero]
    rw [← Polynomial.coeff_zero_eq_eval_zero,
      Polynomial.coeff_derivative]
    norm_num
  have hcoef := paperFixedBindingPrintedCoefficient_eq_physical_ratio
    m ξ r τ ε ω j hr hD₀ hk hx heq hET hFT
  change arbitrarySplitGenericPhysicalPrefactor m ξ r 0
      (paperFixedBindingSplitRates m ξ r 0 ε (Fin.lastCases τ ω)) j /
    J₀.charpoly.derivative.eval 0 = paperFixedBindingPrintedCoefficient m r τ ε ω
  rw [hder]
  simpa only [paperFixedBindingSplitRates,
    arbitrarySplitFiniteRates_zero_eq_coalesced,
    coalescedAllScaledRates] using hcoef

end

end PhosphorylationStableCapacity
