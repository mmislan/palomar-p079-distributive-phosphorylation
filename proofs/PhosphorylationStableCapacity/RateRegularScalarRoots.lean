module
public import proofs.PhosphorylationStableCapacity.RatioCurveRegularDet
public import proofs.PhosphorylationStableCapacity.RatioResidualRootBudget
public import proofs.PhosphorylationStableCapacity.RateRegularBudget

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section
open PhosphorylationSharpness

/-- Arbitrarily close positive literal rate lists have finitely many
positive roots of the exact scalar residual, at most `2n`, and every
such root is simple. -/
theorem nearby_positive_rates_finite_simple_scalar_roots_budget {n : ℕ}
    (hn : 0 < n) (ET FT ST : ℝ)
    (hET : 0 < ET) (hFT : 0 < FT) (hST : 0 < ST)
    (k : Rates n) (hk : k.Positive)
    {U : Set (CoordinateSpace n)} (hU : IsOpen U)
    (hzero : (0 : CoordinateSpace n) ∈ U) :
    ∃ v ∈ U, (ratesAdd k (selectedRates v)).Positive ∧
      let k' := ratesAdd k (selectedRates v)
      let R : Set ℝ :=
        {u | 0 < u ∧ ratioEnzymeResidual k' ET FT ST u = 0}
      R.Finite ∧ R.ncard ≤ 2*n ∧
        ∀ u ∈ R, deriv (ratioEnzymeResidual k' ET FT ST) u ≠ 0 := by
  obtain ⟨v, hvU, hvpos, hregular⟩ :=
    nearby_positive_rates_finite_regular_budget
      hn ET FT ST hET hFT k hk hU hzero
  let k' := ratesAdd k (selectedRates v)
  obtain ⟨hfinite, hbudget⟩ :=
    positive_ratio_residual_roots_finite_and_ncard_le_two_n
      hn k' hvpos ET FT ST hET hFT hST
  refine ⟨v, hvU, hvpos, hfinite, hbudget, ?_⟩
  intro u hu
  let x := ratioEquilibriumCurve k' FT ST u
  have hcurve := ratioEquilibriumCurve_positive_equilibrium_and_totals
    hn k' hvpos FT ST u hFT hST hu.1
  obtain ⟨hx, heq, hF, hS, hE, _hratio⟩ := hcurve
  have hgap := ratioEnzymeResidual_eq_curve_total_gap
    hn k' hvpos ET FT ST u hST hu.1
  have hs :=
    (modelRatioSubstrateLevel_pos_and_inventory
      hn k' hvpos FT ST u hST hu.1).1
  have hD := phosphataseComplexInventory_pos k' hvpos hu.1 hn
  have hden : 0 < 1 + modelRatioSubstrateLevel k' FT ST u *
      phosphataseComplexInventory k' u := by
    nlinarith [mul_pos hs hD]
  rw [hu.2] at hgap
  have hETcurve : ratioCurveKinaseTotal k' FT ST u = ET := by
    have h := (mul_eq_zero.mp hgap.symm).resolve_left
      (ne_of_gt hden)
    linarith
  have hclass : InClass ET FT ST x :=
    ⟨hE.trans hETcurve, hF, hS⟩
  have hdet : (restrictedJacobianMatrix ET FT ST k'
      (ratioEquilibriumCurveChart k' FT ST u)).det ≠ 0 := by
    exact hregular.2.2 x ⟨hx, heq, hclass⟩
  exact ratio_residual_deriv_ne_zero_of_regular_jacobian
    hn k' hvpos ET FT ST u hFT hST hu.1 hu.2 hdet

end
end PhosphorylationStableCapacity
