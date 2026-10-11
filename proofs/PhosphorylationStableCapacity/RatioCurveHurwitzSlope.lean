module
public import proofs.PhosphorylationStableCapacity.RatioCurveDeterminantOrientation
public import proofs.PhosphorylationStableCapacity.SignedNegativeFieldIndex

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section
open PhosphorylationSharpness

theorem coordinate_parity_pow_eq_site_pow (n : ℕ) :
    (-1 : ℝ)^Fintype.card (Fin n ⊕ (Fin n ⊕ Fin n)) =
      (-1 : ℝ)^n := by
  simp only [Fintype.card_sum, Fintype.card_fin]
  rw [show n+(n+n)=n+2*n by omega, pow_add, pow_mul]
  norm_num

/-- Every Hurwitz positive literal equilibrium sits at an increasing
root of the exact scalar residual. -/
theorem hurwitz_positive_equilibrium_has_positive_residual_deriv
    {n : ℕ} (hn : 0 < n) (k : Rates n) (hk : k.Positive)
    (ET FT ST : ℝ) (hFT : 0 < FT) (hST : 0 < ST)
    (z : State n) (hz : z.Positive)
    (heq : Equilibrium k z) (hclass : InClass ET FT ST z)
    (hHurwitz : IsHurwitz (restrictedJacobianMatrix ET FT ST k
      (toCoordinateSpace (chart z)))) :
    0 < deriv (ratioEnzymeResidual k ET FT ST) (z.E/z.F) := by
  let u := z.E/z.F
  have hu : 0 < u := div_pos hz.2.1 hz.2.2.1
  have hroot : ratioEnzymeResidual k ET FT ST u = 0 :=
    positive_equilibrium_ratioEnzymeResidual_zero
      hn k hk ET FT ST hFT hST z hz heq hclass
  let x := ratioEquilibriumCurve k FT ST u
  obtain ⟨hx, heqx, hFx, hSx, _hEx, hratio⟩ :=
    ratioEquilibriumCurve_positive_equilibrium_and_totals
      hn k hk FT ST u hFT hST hu
  have hzx : z = x :=
    positive_equilibria_enzyme_ratio_injective
      k z x hn hk hz hx heq heqx
      (hclass.2.1.trans hFx.symm)
      (hclass.2.2.trans hSx.symm)
      (by simpa only [u] using hratio.symm)
  have hJ : 0 < (-1 : ℝ)^n *
      (restrictedJacobianMatrix ET FT ST k
        (ratioEquilibriumCurveChart k FT ST u)).det := by
    have h := isHurwitz_parity_det_pos _ hHurwitz
    rw [coordinate_parity_pow_eq_site_pow] at h
    simpa only [hzx, x, ratioEquilibriumCurveChart] using h
  exact (ratio_curve_jacobian_sign_iff_residual_deriv
    hn k hk ET FT ST u hFT hST hu hroot).mp hJ

end
end PhosphorylationStableCapacity
