module
import all proofs.PhosphorylationStableCapacity.Jacobian
public import proofs.PhosphorylationStableCapacity.RatioCurveFieldFactor

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section
open PhosphorylationSharpness Filter
open scoped Topology

def ratioCurveKinaseDirection {n : ℕ} (k : Rates n)
    (FT ST u : ℝ) : CoordinateSpace n :=
  kinaseInputDirection k (ratioEquilibriumCurve k FT ST u)

theorem ratioCurveKinaseDirection_differentiableAt {n : ℕ}
    (hn : 0 < n) (k : Rates n) (hk : k.Positive)
    (FT ST u : ℝ) (hST : 0 < ST) (hu : 0 < u) :
    DifferentiableAt ℝ (ratioCurveKinaseDirection k FT ST) u := by
  have hs := modelRatioSubstrateLevel_differentiableAt
    hn k hk FT ST u hST hu
  unfold ratioCurveKinaseDirection kinaseInputDirection
    ratioEquilibriumCurve ratioProfileState
  dsimp
  fun_prop (disch := assumption)

/-- The restricted class Jacobian applied to the tangent of the
literal equilibrium curve is determined exactly by the derivative of
its attained kinase total. -/
theorem restrictedJacobian_ratio_curve_tangent {n : ℕ}
    (hn : 0 < n) (k : Rates n) (hk : k.Positive)
    (ET FT ST u : ℝ) (hFT : 0 < FT) (hST : 0 < ST)
    (hu : 0 < u)
    (hroot : ratioEnzymeResidual k ET FT ST u = 0) :
    restrictedJacobian ET FT ST k
      (ratioEquilibriumCurveChart k FT ST u)
        (deriv (ratioEquilibriumCurveChart k FT ST) u) =
      -(deriv (ratioCurveKinaseTotal k FT ST) u) •
        ratioCurveKinaseDirection k FT ST u := by
  let q := ratioEquilibriumCurveChart k FT ST
  let a : ℝ → ℝ := fun v => ET-ratioCurveKinaseTotal k FT ST v
  let v := ratioCurveKinaseDirection k FT ST
  let F := restrictedFieldEuclid ET FT ST k
  have hq : DifferentiableAt ℝ q u :=
    ratioEquilibriumCurveChart_differentiableAt
      hn k hk FT ST u hST hu
  have ha : DifferentiableAt ℝ a u :=
    (ratioCurveKinaseTotal_differentiableAt
      hn k hk FT ST u hST hu).const_sub ET
  have hv : DifferentiableAt ℝ v u :=
    ratioCurveKinaseDirection_differentiableAt
      hn k hk FT ST u hST hu
  have hF : Differentiable ℝ F :=
    differentiable_restrictedFieldEuclid ET FT ST k
  have hagap : a u = 0 := by
    have hfactor := ratioEnzymeResidual_eq_curve_total_gap
      hn k hk ET FT ST u hST hu
    have hs :=
      (modelRatioSubstrateLevel_pos_and_inventory
        hn k hk FT ST u hST hu).1
    have hD := phosphataseComplexInventory_pos k hk hu hn
    have hden : 0 < 1+modelRatioSubstrateLevel k FT ST u *
        phosphataseComplexInventory k u := by
      nlinarith [mul_pos hs hD]
    rw [hroot] at hfactor
    have hgap := (mul_eq_zero.mp hfactor.symm).resolve_left
      (ne_of_gt hden)
    dsimp [a]
    linarith
  have heq : (fun t => F (q t)) =ᶠ[𝓝 u]
      (fun t => a t • v t) := by
    have hpos : Set.Ioi (0 : ℝ) ∈ 𝓝 u := isOpen_Ioi.mem_nhds hu
    filter_upwards [hpos] with t ht
    exact restrictedField_on_ratioEquilibriumCurveChart
      hn k hk ET FT ST t hFT hST ht
  have hchain := (hF (q u)).hasFDerivAt.comp u hq.hasFDerivAt
  have hprod := ha.hasDerivAt.smul hv.hasDerivAt
  have hsame := heq.deriv_eq
  have hchain' : deriv (fun t => F (q t)) u =
      restrictedJacobian ET FT ST k (q u) (deriv q u) := by
    have h := hchain.hasDerivAt.deriv
    simpa only [Function.comp_def, F, restrictedJacobian,
      ContinuousLinearMap.comp_apply,
      fderiv_apply_one_eq_deriv] using h
  have hprod' : deriv (fun t => a t • v t) u =
      a u • deriv v u + deriv a u • v u := by
    change deriv (a • v) u = _
    exact hprod.deriv
  rw [hchain', hprod', hagap] at hsame
  simpa [q, a, v, F] using hsame

end
end PhosphorylationStableCapacity
