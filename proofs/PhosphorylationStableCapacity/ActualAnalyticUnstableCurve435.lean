module
public import proofs.PhosphorylationStableCapacity.UnstableCurveNonresonance435
public import proofs.PhosphorylationStableCapacity.ActualQuadraticClassField435
public import proofs.PhosphorylationStableCapacity.QuadraticParameterSeries435
public import proofs.PhosphorylationStableCapacity.AnalyticCurveEmbedding435
public import proofs.PhosphorylationStableCapacity.BackwardParameterTrajectory435
public import proofs.PhosphorylationStableCapacity.UniformRealResolvent435
public import Mathlib.Analysis.Analytic.Constructions
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Topology.MetricSpace.Pseudo.Defs

@[expose] public section
namespace P079UnstableWorkbench
open PhosphorylationStableCapacity PhosphorylationStableCapacity.UnstableCurve
open scoped Topology
open Filter

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- A generic actual quadratic saddle has a genuinely constructed analytic
embedded local unstable curve, with explicit invariant backward trajectories.
The hypotheses concern the field and its linearization; no curve is assumed. -/
theorem quadratic_field_analytic_unstable_curve
    (F : E → E) (u v : E) (A : E →L[ℝ] E) (Q : E →L[ℝ] E →L[ℝ] E)
    (lam : ℝ) (hlam : 0 < lam) (hv : v ≠ 0) (heigen : A v = lam • v)
    (hinv : ∀ j : ℕ, 2 ≤ j → IsUnit (((j : ℝ)*lam) • (1:E →L[ℝ] E)-A))
    (hF : ∀ w : E, F (u+w) = A w + Q w w) :
    ∃ (h : ℝ → E) (eps : ℝ), 0 < eps ∧ h 0 = u ∧ deriv h 0 = v ∧
      AnalyticOnNhd ℝ h (Metric.ball (0:ℝ) eps) ∧
      Topology.IsEmbedding (fun s : Metric.ball (0:ℝ) eps => h s) ∧
      (∀ s ∈ Metric.ball (0:ℝ) eps, deriv h s ≠ 0) ∧
      (∀ s ∈ Metric.ball (0:ℝ) eps, (lam*s) • deriv h s = F (h s)) ∧
      ∀ s ∈ Metric.ball (0:ℝ) eps,
        (∀ t : ℝ, t ≤ 0 → h (s*Real.exp (lam*t)) ∈ h '' Metric.ball (0:ℝ) eps ∧
          HasDerivAt (fun z : ℝ => h (s*Real.exp (lam*z)))
            (F (h (s*Real.exp (lam*t)))) t) ∧
        Tendsto (fun t : ℝ => h (s*Real.exp (lam*t))) atBot (𝓝 u) := by
  obtain ⟨M, hM, hbound, hsolve⟩ :=
    harmonicResolvent_uniform_bound_and_solve_of_ge_two A lam hlam hinv
  let R := harmonicResolvent A lam
  let p := vectorSeries (parameterCoefficients R Q v)
  let h : ℝ → E := fun s => u+p.sum s
  have hrad : 0 < p.radius := parameterSeries_positive_radius R Q v M hM.le hbound
  have hseries := p.hasFPowerSeriesOnBall hrad
  have hp0 : p.sum 0 = 0 := parameterSeries_sum_zero R Q v M hM.le hbound
  have h0 : h 0 = u := by simp only [h, hp0, add_zero]
  have ha : AnalyticAt ℝ h 0 := analyticAt_const.add hseries.analyticAt
  have hD0 : fderiv ℝ h 0 1 = v := by
    have hd := (hseries.hasFPowerSeriesAt.hasFDerivAt).const_add u
    rw [hd.fderiv, ← hseries.hasFPowerSeriesAt.fderiv_eq]
    exact parameterSeries_derivative_zero R Q v M hM.le hbound
  obtain ⟨U, hUopen, hU0, hUembed, hUimm⟩ := analyticCurve_open_embedding h v ha hv hD0
  have hnbhd : U ∩ Metric.eball (0:ℝ) p.radius ∈ 𝓝 (0:ℝ) :=
    inter_mem (hUopen.mem_nhds hU0) (Metric.eball_mem_nhds _ hrad)
  obtain ⟨eps, heps, hball⟩ := Metric.mem_nhds_iff.mp hnbhd
  have hdisk {s : ℝ} (hs : s ∈ Metric.ball (0:ℝ) eps) : ‖s‖ₑ < p.radius := by
    simpa using (hball hs).2
  have hanalytic : AnalyticOnNhd ℝ h (Metric.ball (0:ℝ) eps) := by
    intro s hs
    exact analyticAt_const.add (hseries.analyticAt_of_mem (hball hs).2)
  have hD {s : ℝ} (hs : s ∈ Metric.ball (0:ℝ) eps) :
      deriv h s = fderiv ℝ p.sum s 1 := by
    have hd := (p.hasFDerivAt_sum (hdisk hs)).const_add u
    change fderiv ℝ h s 1 = fderiv ℝ p.sum s 1
    rw [hd.fderiv, p.fderiv_sum (hdisk hs)]
  have hinvariant : ∀ s ∈ Metric.ball (0:ℝ) eps, (lam*s) • deriv h s = F (h s) := by
    intro s hs
    rw [hD hs, constructed_parameterSeries_quadratic_invariance R Q v A lam heigen hsolve
      s (hdisk hs)]
    exact (hF (p.sum s)).symm
  have hsub : Metric.ball (0:ℝ) eps ⊆ U := fun s hs => (hball hs).1
  have hembed : Topology.IsEmbedding (fun s : Metric.ball (0:ℝ) eps => h s) := by
    simpa only [Function.comp_def] using hUembed.comp (Topology.IsEmbedding.inclusion hsub)
  refine ⟨h, eps, heps, h0, hD0, hanalytic, hembed,
    (fun s hs => hUimm s (hsub hs)), hinvariant, ?_⟩
  intro s hs
  have hsnorm : ‖s‖ < eps := by simpa only [Metric.mem_ball, dist_zero_right] using hs
  refine ⟨?_, ?_⟩
  · intro t ht
    have htnorm : ‖s*Real.exp (lam*t)‖ < eps :=
      (backwardParameter_norm_le lam s t hlam.le ht).trans_lt hsnorm
    have htmem : s*Real.exp (lam*t) ∈ Metric.ball (0:ℝ) eps := by
      simpa only [Metric.mem_ball, dist_zero_right] using htnorm
    refine ⟨⟨s*Real.exp (lam*t), htmem, rfl⟩, ?_⟩
    exact backwardParameterTrajectory_hasDerivAt h F lam eps s t hlam.le hsnorm ht
      (fun x hx => (hanalytic x (by simpa only [Metric.mem_ball, dist_zero_right] using hx)).differentiableAt.hasDerivAt)
      (fun x hx => hinvariant x (by simpa only [Metric.mem_ball, dist_zero_right] using hx))
  · rw [← h0]
    exact backwardParameterTrajectory_tendsto h lam s hlam ha.continuousAt

/-- Actual smooth mass-action class field endpoint at any currently proved
one-unstable saddle equilibrium. The analytic curve and all backward solutions
are derived from those existing hypotheses. -/
theorem actual_saddle_analytic_unstable_curve
    {n : ℕ} (ET FT ST : ℝ) (k : PhosphorylationSharpness.Rates n)
    (u : CoordinateSpace n) (heq : restrictedFieldEuclid ET FT ST k u = 0)
    (hsaddle : IsOneUnstableSaddle ET FT ST k u) :
    ∃ (lam : ℝ) (v : CoordinateSpace n) (h : ℝ → CoordinateSpace n) (eps : ℝ),
      0 < lam ∧ v ≠ 0 ∧ restrictedJacobian ET FT ST k u v = lam • v ∧
      0 < eps ∧ h 0 = u ∧ deriv h 0 = v ∧
      AnalyticOnNhd ℝ h (Metric.ball (0:ℝ) eps) ∧
      Topology.IsEmbedding (fun s : Metric.ball (0:ℝ) eps => h s) ∧
      (∀ s ∈ Metric.ball (0:ℝ) eps, deriv h s ≠ 0) ∧
      (∀ s ∈ Metric.ball (0:ℝ) eps,
        (lam*s) • deriv h s = restrictedFieldEuclid ET FT ST k (h s)) ∧
      ∀ s ∈ Metric.ball (0:ℝ) eps,
        (∀ t : ℝ, t ≤ 0 → h (s*Real.exp (lam*t)) ∈ h '' Metric.ball (0:ℝ) eps ∧
          HasDerivAt (fun z : ℝ => h (s*Real.exp (lam*z)))
            (restrictedFieldEuclid ET FT ST k (h (s*Real.exp (lam*t)))) t) ∧
        Tendsto (fun t : ℝ => h (s*Real.exp (lam*t))) atBot (𝓝 u) := by
  obtain ⟨lam, v, hlam, hv, heigen, hinv⟩ := actual_saddle_real_operator_data
    ET FT ST k u hsaddle
  have hF (w : CoordinateSpace n) : restrictedFieldEuclid ET FT ST k (u+w) =
      restrictedJacobian ET FT ST k u w + classFieldQuadratic k w w := by
    rw [actual_classField_exact_quadratic_remainder, heq, zero_add]
  obtain ⟨h, eps, hcurve⟩ := quadratic_field_analytic_unstable_curve
    (restrictedFieldEuclid ET FT ST k) u v (restrictedJacobian ET FT ST k u)
    (classFieldQuadratic k) lam hlam hv heigen hinv hF
  exact ⟨lam, v, h, eps, hlam, hv, heigen, hcurve⟩

end P079UnstableWorkbench
