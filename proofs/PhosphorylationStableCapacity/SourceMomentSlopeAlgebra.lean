module
public import proofs.PhosphorylationStableCapacity.SourceJacobianAugmentedOrientation
public import proofs.PhosphorylationStableCapacity.RatioCurveDerivative
public import proofs.PhosphorylationStableCapacity.RatioCurveChart
public import proofs.PhosphorylationStableCapacity.SourceMomentPivotPositive

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section
open PhosphorylationSharpness

/-- Algebraic orientation identity for a one-parameter equilibrium
curve. The first equation is the fixed substrate-total slope; the
second is the varying kinase-total slope in log-ratio coordinates. -/
theorem moment_bracket_mul_total_eq_slope
    (T0 T1 Q0 Q1 C a ET u dET : ℝ)
    (hsubstrate : ET*(T0*a + T1) + C*u*dET = 0)
    (henzyme : ET*(1 - Q1 - Q0*a) = u*dET) :
    ET*((1-Q1)*T0 + Q0*T1) =
      (T0-Q0*C)*u*dET := by
  linear_combination T0*henzyme + Q0*hsubstrate

theorem moment_bracket_pos_iff_total_slope_pos
    (T0 T1 Q0 Q1 C a ET u dET : ℝ)
    (hpivot : 0 < T0-Q0*C) (hET : 0 < ET) (hu : 0 < u)
    (hsubstrate : ET*(T0*a + T1) + C*u*dET = 0)
    (henzyme : ET*(1 - Q1 - Q0*a) = u*dET) :
    0 < (1-Q1)*T0 + Q0*T1 ↔ 0 < dET := by
  have h := moment_bracket_mul_total_eq_slope
    T0 T1 Q0 Q1 C a ET u dET hsubstrate henzyme
  constructor
  · intro hp
    have hprod : 0 < (T0-Q0*C)*u*dET := by
      rw [← h]
      exact mul_pos hET hp
    exact (mul_pos_iff_of_pos_left (mul_pos hpivot hu)).mp
      (by simpa only [mul_assoc] using hprod)
  · intro hd
    have hprod : 0 < ET*((1-Q1)*T0+Q0*T1) := by
      rw [h]
      exact mul_pos (mul_pos hpivot hu) hd
    exact (mul_pos_iff_of_pos_left hET).mp hprod

/-- Exact remaining differential interface for the all-size
determinant/scalar orientation. The two hypotheses are the substrate
inventory slope and kinase inventory slope in log-ratio coordinates.
They are not inferred from the equilibrium equation here. -/
theorem ratio_curve_jacobian_sign_iff_residual_deriv_of_log_slopes
    {n : ℕ} (hn : 0 < n)
    (k : Rates n) (hk : k.Positive)
    (ET FT ST u a : ℝ)
    (hFT : 0 < FT) (hST : 0 < ST) (hu : 0 < u)
    (hroot : ratioEnzymeResidual k ET FT ST u = 0)
    (hsubstrate :
      let x := ratioEquilibriumCurve k FT ST u
      totalE x *
          (sourcePathZerothMoment (sourceAugmentedTotalRow x)*a +
            sourcePathFirstMoment (sourceAugmentedTotalRow x)) +
        (∑ i : Fin n, x.C i)*u*
          deriv (ratioCurveKinaseTotal k FT ST) u = 0)
    (henzyme :
      let x := ratioEquilibriumCurve k FT ST u
      totalE x * (1 -
        sourcePathFirstMoment (sourceOccupancyDifference x) -
        sourcePathZerothMoment (sourceOccupancyDifference x)*a) =
        u*deriv (ratioCurveKinaseTotal k FT ST) u) :
    0 < (-1 : ℝ)^n *
      (restrictedJacobianMatrix ET FT ST k
        (ratioEquilibriumCurveChart k FT ST u)).det ↔
    0 < deriv (ratioEnzymeResidual k ET FT ST) u := by
  let x := ratioEquilibriumCurve k FT ST u
  obtain ⟨hx, heq, hF, hS, hE, _⟩ :=
    ratioEquilibriumCurve_positive_equilibrium_and_totals
      hn k hk FT ST u hFT hST hu
  have hden : 0 < 1 + modelRatioSubstrateLevel k FT ST u *
      phosphataseComplexInventory k u := by
    have hs := (modelRatioSubstrateLevel_pos_and_inventory
      hn k hk FT ST u hST hu).1
    have hD := phosphataseComplexInventory_pos k hk hu hn
    nlinarith [mul_pos hs hD]
  have hgap := ratioEnzymeResidual_eq_curve_total_gap
    hn k hk ET FT ST u hST hu
  rw [hroot] at hgap
  have hE' : totalE x = ET := by
    have hzero := (mul_eq_zero.mp hgap.symm).resolve_left
      (ne_of_gt hden)
    linarith
  let T0 := sourcePathZerothMoment (sourceAugmentedTotalRow x)
  let T1 := sourcePathFirstMoment (sourceAugmentedTotalRow x)
  let Q0 := sourcePathZerothMoment (sourceOccupancyDifference x)
  let Q1 := sourcePathFirstMoment (sourceOccupancyDifference x)
  let C := ∑ i : Fin n, x.C i
  let dET := deriv (ratioCurveKinaseTotal k FT ST) u
  have hpivot : 0 < T0-Q0*C := source_moment_pivot_pos x hx
  have hETpos' : 0 < totalE x := by
    dsimp [totalE]
    exact add_pos_of_pos_of_nonneg hx.2.1
      (Finset.sum_nonneg fun i _ => (hx.2.2.2.1 i).le)
  have hmoment := moment_bracket_pos_iff_total_slope_pos
    T0 T1 Q0 Q1 C a (totalE x) u dET hpivot hETpos' hu
    hsubstrate henzyme
  have hJ := equilibrium_restricted_jacobian_parity_det_pos_iff_moment
    k x hk hx heq
  rw [hE', hF, hS] at hJ
  change 0 < (-1 : ℝ)^n *
      (restrictedJacobianMatrix ET FT ST k
        (ratioEquilibriumCurveChart k FT ST u)).det ↔
      0 < (1-Q1)*T0+Q0*T1 at hJ
  have hR := ratioEnzymeResidual_deriv_at_root_eq_curve_total_deriv
    hn k hk ET FT ST u hST hu hroot
  have hRpos : 0 < deriv (ratioEnzymeResidual k ET FT ST) u ↔
      0 < dET := by
    rw [hR]
    exact mul_pos_iff_of_pos_left hden
  exact hJ.trans (hmoment.trans hRpos.symm)

end
end PhosphorylationStableCapacity
