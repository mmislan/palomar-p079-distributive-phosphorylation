module
public import proofs.PhosphorylationSharpness.Source
public import Mathlib.Algebra.Order.BigOperators.Group.Finset

@[expose] public section

namespace PhosphorylationStableCapacity

open PhosphorylationSharpness

/-- Every positive literal n-site state under positive catalytic rates
has strictly positive total irreversible phosphorylation flux. The
result applies in particular to every positive split equilibrium. -/
theorem positive_total_phosphorylation_flux
    (n : ℕ) (k : Rates (n+1)) (x : State (n+1))
    (hk : k.Positive) (hx : x.Positive) :
    0 < ∑ i : Fin (n+1), k.gamma i * x.D i := by
  apply Finset.sum_pos
  · intro i hi
    exact mul_pos (hk i).2.2.2.2.2 (hx.2.2.2.2 i)
  · exact Finset.univ_nonempty

end PhosphorylationStableCapacity
