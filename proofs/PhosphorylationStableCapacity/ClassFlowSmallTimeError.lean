module
public import proofs.PhosphorylationStableCapacity.ClassInwardTimeHomotopy

@[expose] public section

namespace PhosphorylationStableCapacity

open PhosphorylationSharpness
open scoped NNReal

noncomputable section

/-- The physical time displacement has a uniform quadratic error
relative to the literal class vector field, on the entire compact
nonnegative compatibility class. -/
theorem exists_physical_flow_quadratic_time_error {n : ℕ}
    (ET FT ST : ℝ) (hET : 0 < ET)
    (k : Rates n) (hk : k.Positive) :
    ∃ D : ℝ, 0 ≤ D ∧
      ∀ (u : classPolytope n ET FT ST) (T : ℝ), 0 ≤ T →
        ‖physicalForwardCurve ET FT ST hET k hk u T - u.1 -
          T • restrictedFieldEuclid ET FT ST k u.1‖ ≤ D * T * T := by
  obtain ⟨K, hLip⟩ :=
    restrictedFieldEuclid_lipschitzOn_classPolytope ET FT ST k
  obtain ⟨C, hC, htime⟩ :=
    exists_physical_forward_curve_time_lipschitz ET FT ST hET k hk
  let D : ℝ := (K : ℝ) * C
  have hD : 0 ≤ D := mul_nonneg K.coe_nonneg hC
  refine ⟨D, hD, ?_⟩
  intro u T hT
  let f := restrictedFieldEuclid ET FT ST k
  let γ := physicalForwardCurve ET FT ST hET k hk u
  let e : ℝ → CoordinateSpace n := fun t => γ t - u.1 - t • f u.1
  have hγ := physicalForwardCurve_spec ET FT ST hET k hk u
  have he0 : e 0 = 0 := by simp [e, γ, hγ.1.1]
  have hderiv : ∀ q ∈ Set.Icc (0 : ℝ) T,
      HasDerivWithinAt e (f (γ q) - f u.1)
        (Set.Icc (0 : ℝ) T) q := by
    intro q hq
    have hγd : HasDerivWithinAt γ (f (γ q))
        (Set.Icc (0 : ℝ) T) q := by
      exact (hγ.1.2 q hq.1).mono Set.Icc_subset_Ici_self
    have hlin : HasDerivWithinAt (fun t : ℝ => t • f u.1)
        (f u.1) (Set.Icc (0 : ℝ) T) q := by
      simpa using ((hasDerivAt_id q).smul_const (f u.1)).hasDerivWithinAt
    have heq : e =
        (γ - fun _ => u.1) - (fun t : ℝ => t • f u.1) := by
      funext t
      simp [e]
    rw [heq]
    exact (hγd.sub_const u.1).sub hlin
  have hbound : ∀ q ∈ Set.Icc (0 : ℝ) T,
      ‖f (γ q) - f u.1‖ ≤ D * T := by
    intro q hq
    have hq0 : 0 ≤ q := hq.1
    have hqT : q ≤ T := hq.2
    have hmem : γ q ∈ classPolytope n ET FT ST := hγ.2 q hq0
    have hfield : ‖f (γ q) - f u.1‖ ≤ (K : ℝ) * dist (γ q) u.1 := by
      simpa [f, dist_eq_norm] using
        hLip.dist_le_mul (γ q) hmem u.1 u.2
    have hspeed : dist (γ q) u.1 ≤ C * q := by
      have h := htime u q 0 hq0 (le_refl 0)
      simpa [γ, hγ.1.1, abs_of_nonneg hq0] using h
    have hstep := mul_le_mul_of_nonneg_left hspeed K.coe_nonneg
    have hfinal := mul_le_mul_of_nonneg_left hqT hD
    calc
      ‖f (γ q) - f u.1‖ ≤ (K : ℝ) * dist (γ q) u.1 := hfield
      _ ≤ (K : ℝ) * (C * q) := hstep
      _ = D * q := by ring
      _ ≤ D * T := hfinal
  have hmv := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    hderiv hbound (convex_Icc (0 : ℝ) T)
      ⟨le_refl 0, hT⟩ ⟨hT, le_refl T⟩
  simpa [e, he0, Real.norm_eq_abs, abs_of_nonneg hT,
    mul_assoc] using hmv

end
end PhosphorylationStableCapacity
