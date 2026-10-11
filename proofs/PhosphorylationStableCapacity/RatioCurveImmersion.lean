module
public import Mathlib.Analysis.Calculus.Deriv.Prod
public import proofs.PhosphorylationStableCapacity.RatioCurveJacobianAction

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section
open PhosphorylationSharpness Filter
open scoped Topology

/-- Recover the free-enzyme ratio from the attained kinase total and
the ordered free class coordinates. -/
def ratioFromTotalAndChart {n : ℕ} (FT : ℝ)
    (p : ℝ × CoordinateSpace n) : ℝ :=
  (p.1 - ∑ i : Fin n, p.2.2.1 i) /
    (FT - ∑ i : Fin n, p.2.2.2 i)

theorem ratioFromTotalAndChart_curve {n : ℕ}
    (hn : 0 < n) (k : Rates n) (hk : k.Positive)
    (FT ST u : ℝ) (hFT : 0 < FT) (hST : 0 < ST)
    (hu : 0 < u) :
    ratioFromTotalAndChart FT
      (ratioCurveKinaseTotal k FT ST u,
        ratioEquilibriumCurveChart k FT ST u) = u := by
  let x := ratioEquilibriumCurve k FT ST u
  obtain ⟨_hx, _heq, hF, _hS, hE, hratio⟩ :=
    ratioEquilibriumCurve_positive_equilibrium_and_totals
      hn k hk FT ST u hFT hST hu
  have hE' : ratioCurveKinaseTotal k FT ST u -
      ∑ i : Fin n, (ratioEquilibriumCurveChart k FT ST u).2.1 i = x.E := by
    change ratioCurveKinaseTotal k FT ST u - ∑ i : Fin n, x.C i = x.E
    dsimp [totalE] at hE
    linarith
  have hF' : FT -
      ∑ i : Fin n, (ratioEquilibriumCurveChart k FT ST u).2.2 i = x.F := by
    change FT - ∑ i : Fin n, x.D i = x.F
    dsimp [totalF] at hF
    linarith
  change (ratioCurveKinaseTotal k FT ST u -
      ∑ i : Fin n, (ratioEquilibriumCurveChart k FT ST u).2.1 i) /
    (FT - ∑ i : Fin n,
      (ratioEquilibriumCurveChart k FT ST u).2.2 i) = u
  rw [hE', hF']
  exact hratio

/-- The curve cannot be stationary simultaneously in its attained
kinase total and all `3n` class coordinates: their values recover the
ratio parameter smoothly. -/
theorem ratio_curve_total_and_chart_deriv_not_both_zero {n : ℕ}
    (hn : 0 < n) (k : Rates n) (hk : k.Positive)
    (FT ST u : ℝ) (hFT : 0 < FT) (hST : 0 < ST)
    (hu : 0 < u) :
    ¬(deriv (ratioCurveKinaseTotal k FT ST) u = 0 ∧
      deriv (ratioEquilibriumCurveChart k FT ST) u = 0) := by
  let G := ratioCurveKinaseTotal k FT ST
  let q := ratioEquilibriumCurveChart k FT ST
  let H := ratioFromTotalAndChart (n := n) FT
  have hG : DifferentiableAt ℝ G u :=
    ratioCurveKinaseTotal_differentiableAt
      hn k hk FT ST u hST hu
  have hq : DifferentiableAt ℝ q u :=
    ratioEquilibriumCurveChart_differentiableAt
      hn k hk FT ST u hST hu
  have hx := (ratioEquilibriumCurve_positive_equilibrium_and_totals
      hn k hk FT ST u hFT hST hu).1
  have hF := (ratioEquilibriumCurve_positive_equilibrium_and_totals
      hn k hk FT ST u hFT hST hu).2.2.1
  have hden : FT - ∑ i : Fin n, (q u).2.2 i ≠ 0 := by
    have hF' : FT - ∑ i : Fin n, (q u).2.2 i =
        (ratioEquilibriumCurve k FT ST u).F := by
      change FT - ∑ i : Fin n, (ratioEquilibriumCurve k FT ST u).D i =
        (ratioEquilibriumCurve k FT ST u).F
      dsimp [totalF] at hF
      linarith
    rw [hF']
    exact ne_of_gt hx.2.2.1
  have hH : DifferentiableAt ℝ H (G u, q u) := by
    change DifferentiableAt ℝ
      (fun p : ℝ × CoordinateSpace n =>
        (p.1 - ∑ i : Fin n, p.2.2.1 i) /
          (FT - ∑ i : Fin n, p.2.2.2 i)) (G u, q u)
    fun_prop (disch := assumption)
  have hpair := hG.hasDerivAt.prodMk hq.hasDerivAt
  have hcomp := (hH.hasFDerivAt.comp_hasDerivAt u hpair).deriv
  have heq : (fun t => H (G t, q t)) =ᶠ[𝓝 u]
      (fun t : ℝ => t) := by
    have hpos : Set.Ioi (0 : ℝ) ∈ 𝓝 u := isOpen_Ioi.mem_nhds hu
    filter_upwards [hpos] with t ht
    exact ratioFromTotalAndChart_curve
      hn k hk FT ST t hFT hST ht
  intro hzero
  have hderivZero : deriv (fun t => H (G t, q t)) u = 0 := by
    change deriv (fun t => H (G t, q t)) u =
      (fderiv ℝ H (G u, q u)) (deriv G u, deriv q u) at hcomp
    rw [hcomp]
    rw [hzero.1, hzero.2]
    change (fderiv ℝ H (G u, q u))
      (0 : ℝ × CoordinateSpace n) = 0
    exact map_zero (fderiv ℝ H (G u, q u))
  have hderivOne : deriv (fun t => H (G t, q t)) u = 1 := by
    rw [heq.deriv_eq]
    simp
  linarith

end
end PhosphorylationStableCapacity
