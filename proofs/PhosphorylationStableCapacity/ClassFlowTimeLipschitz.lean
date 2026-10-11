module
public import proofs.PhosphorylationStableCapacity.ClassUniformAttraction
public import Mathlib.Analysis.Calculus.MeanValue

@[expose] public section

namespace PhosphorylationStableCapacity

open PhosphorylationSharpness

noncomputable section

/-- The compact nonnegative class gives one bound on the time speed of
every physical trajectory, for all forward times. -/
theorem exists_physical_forward_curve_time_lipschitz {n : ℕ}
    (ET FT ST : ℝ) (hET : 0 < ET)
    (k : Rates n) (hk : k.Positive) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (u : classPolytope n ET FT ST) (s t : ℝ),
        0 ≤ s → 0 ≤ t →
        dist (physicalForwardCurve ET FT ST hET k hk u s)
          (physicalForwardCurve ET FT ST hET k hk u t) ≤ C * |s - t| := by
  obtain ⟨B, hB⟩ := restrictedFieldEuclid_norm_bound_classPolytope ET FT ST k
  let C := max 0 B
  have hC : 0 ≤ C := le_max_left _ _
  refine ⟨C, hC, ?_⟩
  intro u s t hs ht
  let γ := physicalForwardCurve ET FT ST hET k hk u
  have hγ := physicalForwardCurve_spec ET FT ST hET k hk u
  have hderiv : ∀ q ∈ Set.Ici (0 : ℝ),
      HasDerivWithinAt γ
        (restrictedFieldEuclid ET FT ST k (γ q))
        (Set.Ici (0 : ℝ)) q := hγ.1.2
  have hbound : ∀ q ∈ Set.Ici (0 : ℝ),
      ‖restrictedFieldEuclid ET FT ST k (γ q)‖ ≤ C := by
    intro q hq
    exact (hB (γ q) (hγ.2 q hq)).trans (le_max_right _ _)
  have hmv := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    hderiv hbound (convex_Ici (0 : ℝ)) hs ht
  simpa [γ, dist_eq_norm, Real.norm_eq_abs, abs_sub_comm,
    norm_sub_rev] using hmv

end
end PhosphorylationStableCapacity
