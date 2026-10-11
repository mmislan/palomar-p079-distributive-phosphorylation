module
public import proofs.PhosphorylationStableCapacity.AttractorBoundaryGap

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section

/-- The zero-free sphere around a possibly nonhyperbolic local
attractor can be chosen below any prescribed positive radius. -/
theorem local_attractor_exists_boundary_gap_below {n : ℕ}
    (ET FT ST : ℝ) (k : PhosphorylationSharpness.Rates n)
    (x : CoordinateSpace n)
    (hx : IsLocallyAsymptoticallyStableClass ET FT ST k x)
    (R : ℝ) (hR : 0 < R) :
    ∃ r ε : ℝ, 0 < r ∧ r < R ∧ 0 < ε ∧
      ∀ y : CoordinateSpace n, dist y x = r →
        ε ≤ ‖restrictedFieldEuclid ET FT ST k y‖ := by
  obtain ⟨δ, hδ, hiso⟩ :=
    locally_asymptotically_stable_class_isolated ET FT ST k x hx
  have hsmall : 0 < min δ R := lt_min hδ hR
  have hiso' : ∀ y : CoordinateSpace n,
      dist y x < min δ R →
      restrictedFieldEuclid ET FT ST k y = 0 → y = x := by
    intro y hy hz
    exact hiso y (lt_of_lt_of_le hy (min_le_left δ R)) hz
  obtain ⟨r, ε, hr, hrsmall, hε, hgap⟩ :=
    isolated_zero_exists_sphere_gap
      (restrictedFieldEuclid ET FT ST k)
      (differentiable_restrictedFieldEuclid ET FT ST k).continuous
      x (min δ R) hsmall hiso'
  exact ⟨r, ε, hr, lt_of_lt_of_le hrsmall (min_le_right δ R), hε, hgap⟩

end
end PhosphorylationStableCapacity
