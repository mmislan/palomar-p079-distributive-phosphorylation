module
public import proofs.PhosphorylationStableCapacity.BilinearLyapunovStability

@[expose] public section

namespace PhosphorylationStableCapacity

open PhosphorylationSharpness

noncomputable section

/-- The operator norm supplies the bilinear bound needed by the
nonlinear remainder estimate. -/
theorem bilinear_energy_operator_bound {n : ℕ}
    (B : CoordinateSpace n →L[ℝ] CoordinateSpace n →L[ℝ] ℝ)
    (v w : CoordinateSpace n) :
    |B v w| ≤ (‖B‖ + 1) * ‖v‖ * ‖w‖ := by
  calc
    |B v w| = ‖B v w‖ := (Real.norm_eq_abs _).symm
    _ ≤ ‖B v‖ * ‖w‖ := (B v).le_opNorm w
    _ ≤ (‖B‖ * ‖v‖) * ‖w‖ :=
      mul_le_mul_of_nonneg_right (B.le_opNorm v) (norm_nonneg w)
    _ ≤ (‖B‖ + 1) * ‖v‖ * ‖w‖ := by
      gcongr
      linarith

/-- For a continuous bilinear form, only global quadratic comparison
and strict dissipation of the literal class Jacobian remain as
certificate hypotheses; bilinear boundedness is automatic. -/
theorem class_las_of_quadratic_lyapunov_certificate {n : ℕ}
    (ET FT ST : ℝ) (k : Rates n)
    (x : CoordinateSpace n)
    (heq : restrictedFieldEuclid ET FT ST k x = 0)
    (B : CoordinateSpace n →L[ℝ] CoordinateSpace n →L[ℝ] ℝ)
    (a b C q : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hC : 0 ≤ C)
    (hq : 0 < q) (hratio : b ≤ a * C^2)
    (hquadratic : ∀ v : CoordinateSpace n,
      a * ‖v‖^2 ≤ B v v ∧ B v v ≤ b * ‖v‖^2)
    (hlinear : ∀ v : CoordinateSpace n,
      B v (restrictedJacobian ET FT ST k x v) +
        B (restrictedJacobian ET FT ST k x v) v ≤
        -q * ‖v‖^2)
    (hexist : ∃ δ : ℝ, 0 < δ ∧
      ∀ u : CoordinateSpace n, dist u x < δ →
        ∃ γ : ℝ → CoordinateSpace n,
          IsForwardClassCurve (restrictedFieldEuclid ET FT ST k) u γ) :
    IsLocallyAsymptoticallyStableClass ET FT ST k x := by
  apply class_las_of_bilinear_lyapunov
    ET FT ST k x heq B a b C (‖B‖ + 1) q
    ha hb hC (by positivity) hq hratio hquadratic
  · exact bilinear_energy_operator_bound B
  · exact hlinear
  · exact hexist

end
end PhosphorylationStableCapacity
