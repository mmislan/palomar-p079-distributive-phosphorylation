module
public import proofs.PhosphorylationStableCapacity.RatioEquilibriumCurve

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section
open PhosphorylationSharpness Filter
open scoped Topology

theorem ratioCurveFreePhosphatase_differentiableAt {n : ℕ}
    (hn : 0 < n) (k : Rates n) (hk : k.Positive)
    (FT ST u : ℝ) (hST : 0 < ST) (hu : 0 < u) :
    DifferentiableAt ℝ (ratioCurveFreePhosphatase k FT ST) u := by
  have hs := modelRatioSubstrateLevel_differentiableAt
    hn k hk FT ST u hST hu
  have hspos :=
    (modelRatioSubstrateLevel_pos_and_inventory
      hn k hk FT ST u hST hu).1
  have hD := phosphataseComplexInventory_pos k hk hu hn
  have hden : 1 + modelRatioSubstrateLevel k FT ST u *
      phosphataseComplexInventory k u ≠ 0 := by
    apply ne_of_gt
    nlinarith [mul_pos hspos hD]
  unfold ratioCurveFreePhosphatase
  simp only [phosphataseComplexInventory]
  fun_prop (disch := assumption)

theorem ratioCurveKinaseTotal_differentiableAt {n : ℕ}
    (hn : 0 < n) (k : Rates n) (hk : k.Positive)
    (FT ST u : ℝ) (hST : 0 < ST)
    (hu : 0 < u) :
    DifferentiableAt ℝ (ratioCurveKinaseTotal k FT ST) u := by
  have hs := modelRatioSubstrateLevel_differentiableAt
    hn k hk FT ST u hST hu
  have hspos :=
    (modelRatioSubstrateLevel_pos_and_inventory
      hn k hk FT ST u hST hu).1
  have hD := phosphataseComplexInventory_pos k hk hu hn
  have hden : 1 + modelRatioSubstrateLevel k FT ST u *
      phosphataseComplexInventory k u ≠ 0 := by
    apply ne_of_gt
    nlinarith [mul_pos hspos hD]
  unfold ratioCurveKinaseTotal ratioCurveFreePhosphatase
  simp only [kinaseComplexInventory, phosphataseComplexInventory]
  fun_prop (disch := assumption)

/-- At a positive scalar root, the residual derivative is a positive
denominator times the derivative of the kinase total along the
equilibrium curve. This is the one-dimensional half of the desired
Jacobian orientation comparison. -/
theorem ratioEnzymeResidual_deriv_at_root_eq_curve_total_deriv {n : ℕ}
    (hn : 0 < n) (k : Rates n) (hk : k.Positive)
    (ET FT ST u : ℝ)
    (hST : 0 < ST) (hu : 0 < u)
    (hroot : ratioEnzymeResidual k ET FT ST u = 0) :
    deriv (ratioEnzymeResidual k ET FT ST) u =
      (1 + modelRatioSubstrateLevel k FT ST u *
        phosphataseComplexInventory k u) *
        deriv (ratioCurveKinaseTotal k FT ST) u := by
  let d : ℝ → ℝ := fun v =>
    1 + modelRatioSubstrateLevel k FT ST v *
      phosphataseComplexInventory k v
  let g := ratioCurveKinaseTotal k FT ST
  let f := ratioEnzymeResidual k ET FT ST
  have hd : DifferentiableAt ℝ d u := by
    have hs := modelRatioSubstrateLevel_differentiableAt
      hn k hk FT ST u hST hu
    dsimp [d]
    simp only [phosphataseComplexInventory]
    fun_prop (disch := assumption)
  have hg : DifferentiableAt ℝ g u :=
    ratioCurveKinaseTotal_differentiableAt
      hn k hk FT ST u hST hu
  have hdupos : 0 < d u := by
    have hs :=
      (modelRatioSubstrateLevel_pos_and_inventory
        hn k hk FT ST u hST hu).1
    have hD := phosphataseComplexInventory_pos k hk hu hn
    dsimp [d]
    nlinarith [mul_pos hs hD]
  have hgap : g u - ET = 0 := by
    have hfactor := ratioEnzymeResidual_eq_curve_total_gap
      hn k hk ET FT ST u hST hu
    dsimp [d, g, f] at *
    rw [hroot] at hfactor
    exact (mul_eq_zero.mp hfactor.symm).resolve_left (ne_of_gt hdupos)
  have heq : f =ᶠ[𝓝 u] (fun v => d v * (g v - ET)) := by
    have hpos : Set.Ioi (0 : ℝ) ∈ 𝓝 u := isOpen_Ioi.mem_nhds hu
    filter_upwards [hpos] with v hv
    exact ratioEnzymeResidual_eq_curve_total_gap
      hn k hk ET FT ST v hST hv
  have hderiv := heq.deriv_eq
  have hprod := (hd.hasDerivAt.mul (hg.hasDerivAt.sub_const ET)).deriv
  have hprod' : deriv (fun v => d v * (g v - ET)) u =
      deriv d u * (g u - ET) + d u * deriv g u := by
    have hfun : d * (fun v => g v - ET) =
        (fun v => d v * (g v - ET)) := by
      funext v
      rfl
    rw [← hfun]
    exact hprod
  calc
    deriv f u = deriv (fun v => d v * (g v - ET)) u := hderiv
    _ = deriv d u * (g u - ET) + d u * deriv g u := hprod'
    _ = d u * deriv g u := by rw [hgap]; ring
    _ = (1 + modelRatioSubstrateLevel k FT ST u *
          phosphataseComplexInventory k u) *
          deriv (ratioCurveKinaseTotal k FT ST) u := rfl

end
end PhosphorylationStableCapacity
