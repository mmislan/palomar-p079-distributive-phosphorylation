module
public import proofs.PhosphorylationStableCapacity.ClassFieldLocalFlow
public import proofs.PhosphorylationStableCapacity.ClassPolytopeTopology

@[expose] public section

namespace PhosphorylationStableCapacity

open PhosphorylationSharpness
open scoped NNReal

noncomputable section

/-- The literal class field has one Lipschitz constant on the entire
compact compatibility polytope. This supplies uniform local ODE data
for continuation arguments, without assuming the class is invariant. -/
theorem restrictedFieldEuclid_lipschitzOn_classPolytope {n : ℕ}
    (ET FT ST : ℝ) (k : Rates n) :
    ∃ K : ℝ≥0, LipschitzOnWith K
      (restrictedFieldEuclid ET FT ST k)
      (classPolytope n ET FT ST) := by
  exact (contDiff_restrictedFieldEuclid_fixed_rates ET FT ST k).contDiffOn
    |>.exists_lipschitzOnWith (by norm_num)
      (classPolytope_convex n ET FT ST)
      (classPolytope_isCompact n ET FT ST)

/-- The literal class field also has a uniform norm bound on the
compatibility polytope. -/
theorem restrictedFieldEuclid_norm_bound_classPolytope {n : ℕ}
    (ET FT ST : ℝ) (k : Rates n) :
    ∃ C : ℝ, ∀ u ∈ classPolytope n ET FT ST,
      ‖restrictedFieldEuclid ET FT ST k u‖ ≤ C := by
  exact (classPolytope_isCompact n ET FT ST).exists_bound_of_continuousOn
    (contDiff_restrictedFieldEuclid_fixed_rates ET FT ST k).continuous.continuousOn

end
end PhosphorylationStableCapacity
