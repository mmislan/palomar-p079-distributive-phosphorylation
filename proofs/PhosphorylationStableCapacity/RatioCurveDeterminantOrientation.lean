module
public import proofs.PhosphorylationStableCapacity.RatioCurveMomentIdentities
public import proofs.PhosphorylationStableCapacity.SourceMomentSlopeAlgebra

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section
open PhosphorylationSharpness

/-- At every positive root of the exact scalar residual, the
parity-adjusted determinant of the literal restricted class Jacobian
has exactly the sign of the scalar residual derivative. -/
theorem ratio_curve_jacobian_sign_iff_residual_deriv {n : ℕ}
    (hn : 0 < n) (k : Rates n) (hk : k.Positive)
    (ET FT ST u : ℝ)
    (hFT : 0 < FT) (hST : 0 < ST) (hu : 0 < u)
    (hroot : ratioEnzymeResidual k ET FT ST u = 0) :
    0 < (-1 : ℝ)^n *
      (restrictedJacobianMatrix ET FT ST k
        (ratioEquilibriumCurveChart k FT ST u)).det ↔
    0 < deriv (ratioEnzymeResidual k ET FT ST) u := by
  let a := ratioCurveSubstrateLogSlope k FT ST u
  obtain ⟨hsubstrate, henzyme⟩ :=
    ratioCurve_exact_moment_slope_identities
      hn k hk FT ST u hFT hST hu
  exact ratio_curve_jacobian_sign_iff_residual_deriv_of_log_slopes
    hn k hk ET FT ST u a hFT hST hu hroot hsubstrate henzyme

end
end PhosphorylationStableCapacity
