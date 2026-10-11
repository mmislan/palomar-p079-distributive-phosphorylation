module
public import proofs.PhosphorylationStableCapacity.Jacobian

@[expose] public section

namespace PhosphorylationStableCapacity

open PhosphorylationSharpness

noncomputable section

/-- At every equilibrium, the exact nonlinear class field has a
uniformly small linearization error relative to displacement.
The derivative is the same literal restricted Jacobian used by the
Hurwitz attainment theorem. -/
theorem restrictedField_linearization_remainder {n : ℕ}
    (ET FT ST : ℝ) (k : Rates n)
    (x : CoordinateSpace n)
    (heq : restrictedFieldEuclid ET FT ST k x = 0) :
    ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
      ∀ u : CoordinateSpace n, dist u x < δ →
        ‖restrictedFieldEuclid ET FT ST k u -
          restrictedJacobian ET FT ST k x (u - x)‖ ≤
          ε * ‖u - x‖ := by
  intro ε hε
  have hderiv : HasFDerivAt
      (restrictedFieldEuclid ET FT ST k)
      (restrictedJacobian ET FT ST k x) x :=
    (differentiable_restrictedFieldEuclid ET FT ST k x).hasFDerivAt
  have hlocal := Asymptotics.isLittleO_iff.mp hderiv.isLittleO hε
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp hlocal
  refine ⟨δ, hδ, ?_⟩
  intro u hu
  have h := hball (Metric.mem_ball.mpr hu)
  simpa [heq] using h

end
end PhosphorylationStableCapacity
