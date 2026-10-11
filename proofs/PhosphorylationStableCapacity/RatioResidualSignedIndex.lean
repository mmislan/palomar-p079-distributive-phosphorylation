module
public import proofs.PhosphorylationStableCapacity.RatioCurveHurwitzSlope
public import proofs.PhosphorylationStableCapacity.RatioResidualSignedCount
public import proofs.PhosphorylationStableCapacity.RatioResidualBijection
public import proofs.PhosphorylationStableCapacity.RateRegularScalarRoots

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section
open PhosphorylationSharpness

/-- The sign convention for the negative restricted field agrees with
the orientation of a simple scalar crossing at every positive equilibrium. -/
theorem signedNegativeFieldIndex_eq_crossingCharge {n : ℕ}
    (hn : 0 < n) (k : Rates n) (hk : k.Positive)
    (ET FT ST : ℝ) (hFT : 0 < FT) (hST : 0 < ST)
    (z : State n) (hz : z.Positive)
    (heq : Equilibrium k z) (hclass : InClass ET FT ST z) :
    signedNegativeFieldIndex ET FT ST k z =
      crossingCharge (ratioEnzymeResidual k ET FT ST) (z.E/z.F) := by
  let u := z.E/z.F
  have hu : 0 < u := div_pos hz.2.1 hz.2.2.1
  have hroot : ratioEnzymeResidual k ET FT ST u = 0 :=
    positive_equilibrium_ratioEnzymeResidual_zero
      hn k hk ET FT ST hFT hST z hz heq hclass
  let x := ratioEquilibriumCurve k FT ST u
  obtain ⟨hx, heqx, hFx, hSx, _, hratio⟩ :=
    ratioEquilibriumCurve_positive_equilibrium_and_totals
      hn k hk FT ST u hFT hST hu
  have hzx : z = x :=
    positive_equilibria_enzyme_ratio_injective
      k z x hn hk hz hx heq heqx
      (hclass.2.1.trans hFx.symm)
      (hclass.2.2.trans hSx.symm)
      (by simpa only [u] using hratio.symm)
  have horient := ratio_curve_jacobian_sign_iff_residual_deriv
    hn k hk ET FT ST u hFT hST hu hroot
  dsimp [signedNegativeFieldIndex, crossingCharge]
  rw [coordinate_parity_pow_eq_site_pow, hzx]
  have hratio' : x.E/x.F = u := hratio
  rw [hratio']
  exact if_congr (by simpa only [x, ratioEquilibriumCurveChart] using horient)
    rfl rfl

/-- For a regular literal rate list, the total signed index of all
positive equilibria in one compatibility class is one. -/
theorem positive_equilibria_signedNegativeFieldIndex_sum_one {n : ℕ}
    (hn : 0 < n) (k : Rates n) (hk : k.Positive)
    (ET FT ST : ℝ) (hET : 0 < ET)
    (hFT : 0 < FT) (hST : 0 < ST)
    (E : Set (State n))
    (hE : E = {z | z.Positive ∧ Equilibrium k z ∧ InClass ET FT ST z})
    (hfinite : E.Finite)
    (R : Set ℝ)
    (hR : R = {u | 0 < u ∧ ratioEnzymeResidual k ET FT ST u = 0})
    (hRfinite : R.Finite)
    (hsimple : ∀ u ∈ R, deriv (ratioEnzymeResidual k ET FT ST) u ≠ 0) :
    ∑ z ∈ hfinite.toFinset, signedNegativeFieldIndex ET FT ST k z = 1 := by
  classical
  have hbij : Set.BijOn (fun z : State n => z.E/z.F) E R := by
    rw [hE, hR]
    exact positive_equilibria_bijOn_ratio_residual_roots
      hn k hk ET FT ST hFT hST
  have hsum :
      (∑ z ∈ hfinite.toFinset, signedNegativeFieldIndex ET FT ST k z) =
      ∑ u ∈ hRfinite.toFinset,
        crossingCharge (ratioEnzymeResidual k ET FT ST) u := by
    apply Finset.sum_nbij (fun z : State n => z.E/z.F)
    · intro z hz
      exact hRfinite.mem_toFinset.mpr
        (hbij.mapsTo (hfinite.mem_toFinset.mp hz))
    · intro z hz w hw hzw
      exact hbij.injOn
        (hfinite.mem_toFinset.mp hz)
        (hfinite.mem_toFinset.mp hw) hzw
    · intro u hu
      obtain ⟨z, hz, hzu⟩ := hbij.surjOn
        (hRfinite.mem_toFinset.mp hu)
      exact ⟨z, hfinite.mem_toFinset.mpr hz, hzu⟩
    · intro z hz
      have hz' := hfinite.mem_toFinset.mp hz
      rw [hE] at hz'
      exact signedNegativeFieldIndex_eq_crossingCharge
        hn k hk ET FT ST hFT hST z hz'.1 hz'.2.1 hz'.2.2
  rw [hsum]
  subst R
  exact ratio_residual_signed_crossing_one hn k hk ET FT ST
    hET hFT hST hRfinite (by
      intro u hu hzero
      exact hsimple u ⟨hu, hzero⟩)

/-- The regularity hypothesis on the literal restricted Jacobian is
enough to discharge the simple-root hypothesis of the signed count. -/
theorem positive_equilibria_signedNegativeFieldIndex_sum_one_of_regular
    {n : ℕ} (hn : 0 < n) (k : Rates n) (hk : k.Positive)
    (ET FT ST : ℝ) (hET : 0 < ET)
    (hFT : 0 < FT) (hST : 0 < ST)
    (E : Set (State n))
    (hE : E = {z | z.Positive ∧ Equilibrium k z ∧ InClass ET FT ST z})
    (hfinite : E.Finite)
    (hregular : ∀ z ∈ E,
      (restrictedJacobianMatrix ET FT ST k
        (toCoordinateSpace (chart z))).det ≠ 0) :
    ∑ z ∈ hfinite.toFinset, signedNegativeFieldIndex ET FT ST k z = 1 := by
  let R : Set ℝ :=
    {u | 0 < u ∧ ratioEnzymeResidual k ET FT ST u = 0}
  have hRfinite : R.Finite :=
    (positive_ratio_residual_roots_finite_and_ncard_le_two_n
      hn k hk ET FT ST hET hFT hST).1
  have hsimple : ∀ u ∈ R,
      deriv (ratioEnzymeResidual k ET FT ST) u ≠ 0 := by
    intro u hu
    let x := ratioEquilibriumCurve k FT ST u
    obtain ⟨hx, heq, hF, hS, hX, _⟩ :=
      ratioEquilibriumCurve_positive_equilibrium_and_totals
        hn k hk FT ST u hFT hST hu.1
    have hgap := ratioEnzymeResidual_eq_curve_total_gap
      hn k hk ET FT ST u hST hu.1
    have hs :=
      (modelRatioSubstrateLevel_pos_and_inventory
        hn k hk FT ST u hST hu.1).1
    have hD := phosphataseComplexInventory_pos k hk hu.1 hn
    have hden : 0 < 1 + modelRatioSubstrateLevel k FT ST u *
        phosphataseComplexInventory k u := by
      nlinarith [mul_pos hs hD]
    rw [hu.2] at hgap
    have hETcurve : ratioCurveKinaseTotal k FT ST u = ET := by
      have h := (mul_eq_zero.mp hgap.symm).resolve_left
        (ne_of_gt hden)
      linarith
    have hclass : InClass ET FT ST x :=
      ⟨hX.trans hETcurve, hF, hS⟩
    have hdet : (restrictedJacobianMatrix ET FT ST k
        (ratioEquilibriumCurveChart k FT ST u)).det ≠ 0 := by
      have hxE : x ∈ E := by
        rw [hE]
        exact ⟨hx, heq, hclass⟩
      exact hregular x hxE
    exact ratio_residual_deriv_ne_zero_of_regular_jacobian
      hn k hk ET FT ST u hFT hST hu.1 hu.2 hdet
  exact positive_equilibria_signedNegativeFieldIndex_sum_one
    hn k hk ET FT ST hET hFT hST E hE hfinite R rfl hRfinite hsimple

end
end PhosphorylationStableCapacity
