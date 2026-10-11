module
public import proofs.PhosphorylationStableCapacity.PaperFixedBindingSchur435

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section
open PhosphorylationSharpness

/-- Pointwise physical source data needed for the derivative chain.
These are exact state, total and mass identities; no spectral conclusion
or eventual large-source threshold is an input. -/
structure PaperCoalescedPhysicalData (m : ℕ) (r : ℝ) : Prop where
  ratesPositive : (coalescedFiniteRates (m+1) r).Positive
  statePositive : (coalescedFiniteState (m+1) r).Positive
  stateEquilibrium : Equilibrium (coalescedFiniteRates (m+1) r)
    (coalescedFiniteState (m+1) r)
  totalE_eq : totalE (coalescedFiniteState (m+1) r) = 2*r
  totalF_eq : totalF (coalescedFiniteState (m+1) r) = 2
  totalS_eq : totalS (coalescedFiniteState (m+1) r) = 2*(r+1)
  sumC_eq : (∑ i : Fin (m+2), (coalescedFiniteState (m+1) r).C i) = 2*r-1
  sumD_eq : (∑ i : Fin (m+2), (coalescedFiniteState (m+1) r).D i) = 1
  sourceNeZero : r ≠ 0
  massDetNeZero : (coalescedFullMass m r).det ≠ 0

end
end PhosphorylationStableCapacity
