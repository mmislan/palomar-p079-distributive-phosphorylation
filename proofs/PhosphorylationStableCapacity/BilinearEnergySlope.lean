module
public import proofs.PhosphorylationStableCapacity.BilinearEnergyChain

@[expose] public section

namespace PhosphorylationStableCapacity

open PhosphorylationSharpness

noncomputable section

/-- A strict quadratic Lyapunov inequality for the literal restricted
Jacobian remains negative for the nonlinear class field nearby.
The Taylor error is obtained from the actual Fréchet derivative. -/
theorem restrictedField_bilinear_slope_negative_near {n : ℕ}
    (ET FT ST : ℝ) (k : Rates n)
    (x : CoordinateSpace n)
    (heq : restrictedFieldEuclid ET FT ST k x = 0)
    (B : CoordinateSpace n →L[ℝ] CoordinateSpace n →L[ℝ] ℝ)
    (M q : ℝ) (hM : 0 < M) (hq : 0 < q)
    (hbound : ∀ v w : CoordinateSpace n,
      |B v w| ≤ M * ‖v‖ * ‖w‖)
    (hlinear : ∀ v : CoordinateSpace n,
      B v (restrictedJacobian ET FT ST k x v) +
        B (restrictedJacobian ET FT ST k x v) v ≤
        -q * ‖v‖^2) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ u : CoordinateSpace n, dist u x < δ →
        B (u-x) (restrictedFieldEuclid ET FT ST k u) +
          B (restrictedFieldEuclid ET FT ST k u) (u-x) ≤
          -(q/2) * ‖u-x‖^2 := by
  let ε : ℝ := q / (4*M)
  have hε : 0 < ε := div_pos hq (by positivity)
  obtain ⟨δ, hδ, hrem⟩ :=
    restrictedField_linearization_remainder ET FT ST k x heq ε hε
  refine ⟨δ, hδ, ?_⟩
  intro u hu
  let v := u-x
  let w := restrictedFieldEuclid ET FT ST k u -
    restrictedJacobian ET FT ST k x v
  have hw : ‖w‖ ≤ ε * ‖v‖ := hrem u hu
  have hBw₁ : B v w ≤ M * ‖v‖ * ‖w‖ :=
    (le_abs_self _).trans (hbound v w)
  have hBw₂ : B w v ≤ M * ‖w‖ * ‖v‖ :=
    (le_abs_self _).trans (hbound w v)
  have hterm :
      M * ‖v‖ * ‖w‖ + M * ‖w‖ * ‖v‖ ≤
        (q/2) * ‖v‖^2 := by
    have hmul : M * ‖v‖ * ‖w‖ ≤
        M * ‖v‖ * (ε * ‖v‖) := by
      exact mul_le_mul_of_nonneg_left hw (by positivity)
    have hmul' : M * ‖w‖ * ‖v‖ ≤
        M * (ε * ‖v‖) * ‖v‖ := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hw hM.le) (norm_nonneg _)
    have hconst : 2 * M * ε = q/2 := by
      dsimp [ε]
      field_simp
      ring
    nlinarith [sq_nonneg ‖v‖]
  have hdecomp : restrictedFieldEuclid ET FT ST k u =
      restrictedJacobian ET FT ST k x v + w := by
    dsimp [w]
    abel
  have hslope :
      B v (restrictedFieldEuclid ET FT ST k u) +
        B (restrictedFieldEuclid ET FT ST k u) v =
      B v (restrictedJacobian ET FT ST k x v) +
        B (restrictedJacobian ET FT ST k x v) v +
          B v w + B w v := by
    rw [hdecomp, map_add, map_add]
    simp
    ring
  change B v (restrictedFieldEuclid ET FT ST k u) +
    B (restrictedFieldEuclid ET FT ST k u) v ≤
      -(q/2) * ‖v‖^2
  rw [hslope]
  have hlin := hlinear v
  linarith

end
end PhosphorylationStableCapacity
