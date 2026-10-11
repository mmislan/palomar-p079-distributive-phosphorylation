module
public import proofs.PhosphorylationStableCapacity.RatioCurveImmersion

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section
open PhosphorylationSharpness

/-- A positive equilibrium with an injective literal restricted
Jacobian is a simple root of the exact scalar residual. -/
theorem ratio_residual_deriv_ne_zero_of_restrictedJacobian_injective
    {n : ℕ} (hn : 0 < n) (k : Rates n) (hk : k.Positive)
    (ET FT ST u : ℝ) (hFT : 0 < FT)
    (hST : 0 < ST) (hu : 0 < u)
    (hroot : ratioEnzymeResidual k ET FT ST u = 0)
    (hJ : Function.Injective (restrictedJacobian ET FT ST k
      (ratioEquilibriumCurveChart k FT ST u))) :
    deriv (ratioEnzymeResidual k ET FT ST) u ≠ 0 := by
  let G := ratioCurveKinaseTotal k FT ST
  let q := ratioEquilibriumCurveChart k FT ST
  have hs :=
    (modelRatioSubstrateLevel_pos_and_inventory
      hn k hk FT ST u hST hu).1
  have hD := phosphataseComplexInventory_pos k hk hu hn
  have hden : 0 < 1 + modelRatioSubstrateLevel k FT ST u *
      phosphataseComplexInventory k u := by
    nlinarith [mul_pos hs hD]
  intro hres
  have hG : deriv G u = 0 := by
    have h := ratioEnzymeResidual_deriv_at_root_eq_curve_total_deriv
      hn k hk ET FT ST u hST hu hroot
    rw [hres] at h
    exact (mul_eq_zero.mp h.symm).resolve_left (ne_of_gt hden)
  have hJq : restrictedJacobian ET FT ST k (q u) (deriv q u) = 0 := by
    have h := restrictedJacobian_ratio_curve_tangent
      hn k hk ET FT ST u hFT hST hu hroot
    simpa only [G, q, hG, neg_zero, zero_smul] using h
  have hq : deriv q u = 0 := by
    apply hJ
    simpa using hJq
  exact ratio_curve_total_and_chart_deriv_not_both_zero
    hn k hk FT ST u hFT hST hu ⟨hG, hq⟩

end
end PhosphorylationStableCapacity
