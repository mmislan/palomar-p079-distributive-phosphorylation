module
public import Mathlib.Analysis.ODE.ExistUnique
public import proofs.PhosphorylationStableCapacity.ClassFieldLocalLipschitz
public import Mathlib.Analysis.ODE.PicardLindelof

@[expose] public section

namespace PhosphorylationStableCapacity

open PhosphorylationSharpness Filter
open scoped Topology

noncomputable section

/-- At every class state, the literal mass-action vector field admits
a local flow with the prescribed initial value and exact derivative. -/
theorem restrictedFieldEuclid_exists_local_flow {n : ℕ}
    (ET FT ST : ℝ) (k : Rates n) (u : CoordinateSpace n) :
    ∃ α : CoordinateSpace n → ℝ → CoordinateSpace n,
      ∀ᶠ xt in 𝓝 u ×ˢ 𝓝 (0 : ℝ),
        α xt.1 0 = xt.1 ∧
          HasDerivAt (α xt.1)
            (restrictedFieldEuclid ET FT ST k (α xt.1 xt.2)) xt.2 := by
  exact (contDiff_restrictedFieldEuclid_fixed_rates ET FT ST k).contDiffAt
    |>.exists_eventually_eq_hasDerivAt 0

end
end PhosphorylationStableCapacity
