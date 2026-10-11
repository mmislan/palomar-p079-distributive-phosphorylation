module
public import proofs.PhosphorylationStableCapacity.ActualAnalyticUnstableCurve435
public import Mathlib.Topology.Order.OrderClosed

@[expose] public section

namespace P079UnstableWorkbench

open PhosphorylationStableCapacity PhosphorylationSharpness Filter
open scoped Topology

noncomputable section

/-- Positivity of every reconstructed concentration is an open condition in
the literal affine coordinates of one fixed compatibility class. -/
theorem isOpen_actualClassPositiveCoordinates {n : ℕ} (ET FT ST : ℝ) :
    IsOpen {u : CoordinateSpace n |
      (unChart ET FT ST (ofCoordinateSpace u)).Positive} := by
  have hS (i : Fin (n+1)) : Continuous (fun u : CoordinateSpace n =>
      (unChart ET FT ST (ofCoordinateSpace u)).S i) := by
    simpa only [unChart_substrate_affine] using
      (continuous_const.fun_add (freeSubstrateCoordinate i).continuous :
        Continuous (fun u : CoordinateSpace n =>
          constantSubstrate ST i + freeSubstrateCoordinate i u))
  have hE : Continuous (fun u : CoordinateSpace n =>
      (unChart ET FT ST (ofCoordinateSpace u)).E) := by
    simpa only [unChart_kinase_affine] using
      (continuous_const.fun_add (freeKinaseCoordinate n).continuous :
        Continuous (fun u : CoordinateSpace n => ET + freeKinaseCoordinate n u))
  have hF : Continuous (fun u : CoordinateSpace n =>
      (unChart ET FT ST (ofCoordinateSpace u)).F) := by
    simpa only [unChart_phosphatase_affine] using
      (continuous_const.fun_add (freePhosphataseCoordinate n).continuous :
        Continuous (fun u : CoordinateSpace n => FT + freePhosphataseCoordinate n u))
  have hC (i : Fin n) : Continuous (fun u : CoordinateSpace n =>
      (unChart ET FT ST (ofCoordinateSpace u)).C i) := by
    change Continuous (fun u : CoordinateSpace n => u.2.1 i)
    exact (continuous_apply i).comp
      (continuous_fst.comp continuous_snd :
        Continuous (fun u : CoordinateSpace n => u.2.1))
  have hD (i : Fin n) : Continuous (fun u : CoordinateSpace n =>
      (unChart ET FT ST (ofCoordinateSpace u)).D i) := by
    change Continuous (fun u : CoordinateSpace n => u.2.2 i)
    exact (continuous_apply i).comp
      (continuous_snd.comp continuous_snd :
        Continuous (fun u : CoordinateSpace n => u.2.2))
  have hSopen : IsOpen {u : CoordinateSpace n |
      ∀ i : Fin (n+1), 0 < (unChart ET FT ST (ofCoordinateSpace u)).S i} := by
    have heq : {u : CoordinateSpace n |
        ∀ i : Fin (n+1), 0 < (unChart ET FT ST (ofCoordinateSpace u)).S i} =
        ⋂ i : Fin (n+1), {u | 0 < (unChart ET FT ST (ofCoordinateSpace u)).S i} := by
      ext u
      simp only [Set.mem_ofPred_eq, Set.mem_iInter]
    rw [heq]
    exact isOpen_iInter_of_finite (fun i => isOpen_lt continuous_const (hS i))
  have hCopen : IsOpen {u : CoordinateSpace n |
      ∀ i : Fin n, 0 < (unChart ET FT ST (ofCoordinateSpace u)).C i} := by
    have heq : {u : CoordinateSpace n |
        ∀ i : Fin n, 0 < (unChart ET FT ST (ofCoordinateSpace u)).C i} =
        ⋂ i : Fin n, {u | 0 < (unChart ET FT ST (ofCoordinateSpace u)).C i} := by
      ext u
      simp only [Set.mem_ofPred_eq, Set.mem_iInter]
    rw [heq]
    exact isOpen_iInter_of_finite (fun i => isOpen_lt continuous_const (hC i))
  have hDopen : IsOpen {u : CoordinateSpace n |
      ∀ i : Fin n, 0 < (unChart ET FT ST (ofCoordinateSpace u)).D i} := by
    have heq : {u : CoordinateSpace n |
        ∀ i : Fin n, 0 < (unChart ET FT ST (ofCoordinateSpace u)).D i} =
        ⋂ i : Fin n, {u | 0 < (unChart ET FT ST (ofCoordinateSpace u)).D i} := by
      ext u
      simp only [Set.mem_ofPred_eq, Set.mem_iInter]
    rw [heq]
    exact isOpen_iInter_of_finite (fun i => isOpen_lt continuous_const (hD i))
  simpa only [State.Positive, Set.ofPred_and] using
    hSopen.inter ((isOpen_lt continuous_const hE).inter
      ((isOpen_lt continuous_const hF).inter (hCopen.inter hDopen)))

/-- The actual analytic unstable curve at a positive saddle stays in the
positive physical compatibility class. The field, totals, base point,
eigenpair and constructed curve are retained; only its radius is shrunk. -/
theorem actual_positive_saddle_analytic_unstable_curve
    {n : ℕ} (ET FT ST : ℝ) (k : Rates n) (u : CoordinateSpace n)
    (hpositive : (unChart ET FT ST (ofCoordinateSpace u)).Positive)
    (heq : restrictedFieldEuclid ET FT ST k u = 0)
    (hsaddle : IsOneUnstableSaddle ET FT ST k u) :
    ∃ (lam : ℝ) (v : CoordinateSpace n) (h : ℝ → CoordinateSpace n) (eps : ℝ),
      0 < lam ∧ v ≠ 0 ∧ restrictedJacobian ET FT ST k u v = lam • v ∧
      0 < eps ∧ h 0 = u ∧ deriv h 0 = v ∧
      AnalyticOnNhd ℝ h (Metric.ball (0:ℝ) eps) ∧
      Topology.IsEmbedding (fun s : Metric.ball (0:ℝ) eps => h s) ∧
      (∀ s ∈ Metric.ball (0:ℝ) eps, deriv h s ≠ 0) ∧
      (∀ s ∈ Metric.ball (0:ℝ) eps,
        (lam*s) • deriv h s = restrictedFieldEuclid ET FT ST k (h s)) ∧
      (∀ s ∈ Metric.ball (0:ℝ) eps,
        (unChart ET FT ST (ofCoordinateSpace (h s))).Positive ∧
        InClass ET FT ST (unChart ET FT ST (ofCoordinateSpace (h s)))) ∧
      ∀ s ∈ Metric.ball (0:ℝ) eps,
        (∀ t : ℝ, t ≤ 0 →
          h (s*Real.exp (lam*t)) ∈ h '' Metric.ball (0:ℝ) eps ∧
          HasDerivAt (fun z : ℝ => h (s*Real.exp (lam*z)))
            (restrictedFieldEuclid ET FT ST k (h (s*Real.exp (lam*t)))) t ∧
          (unChart ET FT ST (ofCoordinateSpace (h (s*Real.exp (lam*t))))).Positive ∧
          InClass ET FT ST
            (unChart ET FT ST (ofCoordinateSpace (h (s*Real.exp (lam*t)))))) ∧
        Tendsto (fun t : ℝ => h (s*Real.exp (lam*t))) atBot (𝓝 u) := by
  obtain ⟨lam, v, h, eps₀, hlam, hv, heigen, heps₀, hzero, hderivzero,
    hanalytic, hembed, himmersion, hinvariant, hbackward⟩ :=
    actual_saddle_analytic_unstable_curve ET FT ST k u heq hsaddle
  have hzeroMem : (0 : ℝ) ∈ Metric.ball 0 eps₀ := by
    simpa only [Metric.mem_ball, dist_self] using heps₀
  have hcont : ContinuousAt h 0 := (hanalytic 0 hzeroMem).continuousAt
  have hphysicalNhd : {s : ℝ |
      (unChart ET FT ST (ofCoordinateSpace (h s))).Positive} ∈ 𝓝 0 := by
    change h ⁻¹' {u : CoordinateSpace n |
      (unChart ET FT ST (ofCoordinateSpace u)).Positive} ∈ 𝓝 0
    apply hcont.preimage_mem_nhds
    apply (isOpen_actualClassPositiveCoordinates ET FT ST).mem_nhds
    change (unChart ET FT ST (ofCoordinateSpace (h 0))).Positive
    rw [hzero]
    exact hpositive
  obtain ⟨eta, heta, hphysicalBall⟩ := Metric.mem_nhds_iff.mp hphysicalNhd
  let eps : ℝ := min eps₀ eta
  have heps : 0 < eps := lt_min heps₀ heta
  have hsub : Metric.ball (0:ℝ) eps ⊆ Metric.ball 0 eps₀ :=
    Metric.ball_subset_ball (min_le_left eps₀ eta)
  have hphysical : ∀ s ∈ Metric.ball (0:ℝ) eps,
      (unChart ET FT ST (ofCoordinateSpace (h s))).Positive ∧
      InClass ET FT ST (unChart ET FT ST (ofCoordinateSpace (h s))) := by
    intro s hs
    exact ⟨hphysicalBall (Metric.ball_subset_ball (min_le_right eps₀ eta) hs),
      unChart_inClass ET FT ST (ofCoordinateSpace (h s))⟩
  have hembedSmall : Topology.IsEmbedding
      (fun s : Metric.ball (0:ℝ) eps => h s) := by
    simpa only [Function.comp_def] using
      hembed.comp (Topology.IsEmbedding.inclusion hsub)
  refine ⟨lam, v, h, eps, hlam, hv, heigen, heps, hzero, hderivzero,
    (fun s hs => hanalytic s (hsub hs)), hembedSmall,
    (fun s hs => himmersion s (hsub hs)),
    (fun s hs => hinvariant s (hsub hs)), hphysical, ?_⟩
  intro s hs
  refine ⟨?_, (hbackward s (hsub hs)).2⟩
  intro t ht
  have hsnorm : ‖s‖ < eps := by
    simpa only [Metric.mem_ball, dist_zero_right] using hs
  have htnorm : ‖s*Real.exp (lam*t)‖ < eps :=
    (backwardParameter_norm_le lam s t hlam.le ht).trans_lt hsnorm
  have htmem : s*Real.exp (lam*t) ∈ Metric.ball (0:ℝ) eps := by
    simpa only [Metric.mem_ball, dist_zero_right] using htnorm
  exact ⟨⟨s*Real.exp (lam*t), htmem, rfl⟩,
    ((hbackward s (hsub hs)).1 t ht).2, hphysical _ htmem⟩

end
end P079UnstableWorkbench
