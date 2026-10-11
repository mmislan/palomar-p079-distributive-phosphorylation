module
public import proofs.PhosphorylationStableCapacity.ClassFlowTimeLipschitz

@[expose] public section

namespace PhosphorylationStableCapacity

open PhosphorylationSharpness
open scoped NNReal

noncomputable section

/-- The literal physical flow is jointly continuous in forward time
and initial state on the entire nonnegative class. -/
theorem physicalForwardCurve_joint_continuousOn {n : ℕ}
    (ET FT ST : ℝ) (hET : 0 < ET)
    (k : Rates n) (hk : k.Positive) :
    ContinuousOn
      (fun p : ℝ × classPolytope n ET FT ST =>
        physicalForwardCurve ET FT ST hET k hk p.2 p.1)
      (Set.Ici (0 : ℝ) ×ˢ Set.univ) := by
  obtain ⟨C, hC, htime⟩ :=
    exists_physical_forward_curve_time_lipschitz ET FT ST hET k hk
  let K : ℝ≥0 := ⟨C, hC⟩
  have hK : (K : ℝ) = C := by rfl
  apply continuousOn_prod_of_continuousOn_lipschitzOnWith
    (K := K)
  · intro t ht
    have hcont : Continuous
        (fun u : classPolytope n ET FT ST =>
          (physicalTimeMap ET FT ST hET k hk t ht u : CoordinateSpace n)) :=
      continuous_subtype_val.comp
        (physicalTimeMap_continuous ET FT ST hET k hk t ht)
    change ContinuousOn
      (fun u : classPolytope n ET FT ST =>
        (physicalTimeMap ET FT ST hET k hk t ht u : CoordinateSpace n))
      Set.univ
    exact hcont.continuousOn
  · intro u _
    apply LipschitzOnWith.of_dist_le_mul
    intro s hs t ht
    have h := htime u s t hs ht
    simpa [hK, Subtype.dist_eq, Real.dist_eq] using h

end
end PhosphorylationStableCapacity
