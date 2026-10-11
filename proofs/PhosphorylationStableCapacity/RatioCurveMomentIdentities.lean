module
public import proofs.PhosphorylationStableCapacity.RatioCurveTotalLogDerivative
public import proofs.PhosphorylationStableCapacity.RatioCurveMomentBalanceAlgebra

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section
open PhosphorylationSharpness

/-- The two coupled log-ratio slope identities for the exact positive
equilibrium curve. They account for the changing kinase total in the
substrate inventory and close the differential input to the all-size
Jacobian orientation comparison. -/
theorem ratioCurve_exact_moment_slope_identities {n : ℕ}
    (hn : 0 < n) (k : Rates n) (hk : k.Positive)
    (FT ST u : ℝ) (hFT : 0 < FT) (hST : 0 < ST)
    (hu : 0 < u) :
    let x := ratioEquilibriumCurve k FT ST u
    let a := ratioCurveSubstrateLogSlope k FT ST u
    let dET := deriv (ratioCurveKinaseTotal k FT ST) u
    (totalE x *
        (sourcePathZerothMoment (sourceAugmentedTotalRow x)*a +
          sourcePathFirstMoment (sourceAugmentedTotalRow x)) +
      (∑ i : Fin n, x.C i)*u*dET = 0) ∧
    (totalE x * (1 -
        sourcePathFirstMoment (sourceOccupancyDifference x) -
        sourcePathZerothMoment (sourceOccupancyDifference x)*a) =
      u*dET) := by
  dsimp only
  let x := ratioEquilibriumCurve k FT ST u
  let a := ratioCurveSubstrateLogSlope k FT ST u
  let b := ratioCurvePhosphataseLogSlope k FT ST u
  let dET := deriv (ratioCurveKinaseTotal k FT ST) u
  let C := ∑ i : Fin n, x.C i
  let D := ∑ i : Fin n, x.D i
  let SS := ∑ j : Fin (n+1), x.S j*(a+(j.val:ℝ))
  let SC := ∑ i : Fin n, x.C i*(a+(i.val:ℝ))
  let SD := ∑ i : Fin n, x.D i*(a+((i.val+1:ℕ):ℝ))
  have hCsplit :
      (∑ i : Fin n, x.C i*(a+b+((i.val+1:ℕ):ℝ))) =
      SC+(b+1)*C := by
    dsimp [SC, C]
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    push_cast
    ring
  have hDsplit :
      (∑ i : Fin n, x.D i*(a+b+((i.val+1:ℕ):ℝ))) =
      SD+b*D := by
    dsimp [SD, D]
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hkin : u*dET = x.E*(1+b)+SC+(b+1)*C := by
    have h := ratioCurve_kinaseTotal_scaled_deriv
      hn k hk FT ST u hFT hST hu
    change u*dET = x.E*(1+b) +
      (∑ i : Fin n, x.C i*(a+b+((i.val+1:ℕ):ℝ))) at h
    rw [hCsplit] at h
    simpa only [add_assoc] using h
  have hphos : x.F*b+SD+b*D=0 := by
    have h := ratioCurve_phosphataseTotal_log_balance
      hn k hk FT ST u hFT hST hu
    change x.F*b +
      (∑ i : Fin n, x.D i*(a+b+((i.val+1:ℕ):ℝ))) = 0 at h
    rw [hDsplit] at h
    linarith
  have hsubstrate : SS+SC+(b+1)*C+SD+b*D=0 := by
    have h := ratioCurve_substrateTotal_log_balance
      hn k hk FT ST u hFT hST hu
    change SS +
      (∑ i : Fin n, x.C i*(a+b+((i.val+1:ℕ):ℝ))) +
      (∑ i : Fin n, x.D i*(a+b+((i.val+1:ℕ):ℝ))) = 0 at h
    rw [hCsplit, hDsplit] at h
    linarith
  have hx : x.Positive :=
    (ratioEquilibriumCurve_positive_equilibrium_and_totals
      hn k hk FT ST u hFT hST hu).1
  have hETpos : 0 < totalE x := by
    dsimp [totalE]
    exact add_pos_of_pos_of_nonneg hx.2.1
      (Finset.sum_nonneg fun i _ => (hx.2.2.2.1 i).le)
  have hFTpos : 0 < totalF x := by
    dsimp [totalF]
    exact add_pos_of_pos_of_nonneg hx.2.2.1
      (Finset.sum_nonneg fun i _ => (hx.2.2.2.2 i).le)
  obtain ⟨hQalg, hTalg⟩ :=
    total_log_balances_imply_moment_identities
      x.E x.F C D (totalE x) (totalF x) SS SC SD b u dET
      rfl rfl (ne_of_gt hETpos) (ne_of_gt hFTpos)
      hkin hphos hsubstrate
  have hQ := sourceOccupancyDifference_affine_moment x a
  have hT := sourceAugmentedTotalRow_affine_moment x hx a
  constructor
  · rw [hT]
    exact hTalg
  · have hQ' :
        sourcePathFirstMoment (sourceOccupancyDifference x) +
        sourcePathZerothMoment (sourceOccupancyDifference x)*a =
        SD/totalF x-SC/totalE x := by
      calc
        _ = sourcePathZerothMoment (sourceOccupancyDifference x)*a +
            sourcePathFirstMoment (sourceOccupancyDifference x) := by ring
        _ = SD/totalF x-SC/totalE x := hQ
    rw [← hQ'] at hQalg
    convert hQalg using 1
    ring

end
end PhosphorylationStableCapacity
