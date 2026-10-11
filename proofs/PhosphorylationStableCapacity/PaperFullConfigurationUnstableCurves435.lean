module
public import proofs.PhosphorylationStableCapacity.RationalFullFamilyAllSizes435
public import proofs.PhosphorylationStableCapacity.ActualPositiveAnalyticUnstableCurve435

@[expose] public section

namespace PhosphorylationStableCapacity

open PhosphorylationSharpness P079UnstableWorkbench Filter
open scoped Topology

noncomputable section

/-- An actual positive analytic unstable curve in the same physical
compatibility class, including its literal backward solutions. -/
def ActualPositiveAnalyticUnstableCurveAt {n : ℕ}
    (ET FT ST : ℝ) (k : Rates n) (u : CoordinateSpace n) : Prop :=
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
      Tendsto (fun t : ℝ => h (s*Real.exp (lam*t))) atBot (𝓝 u)

/-- The rational full-configuration clauses are retained at fixed common
rates, totals and indexed class coordinates before adding any curves. -/
def PaperRationalFullConfigurationAt {n : ℕ}
    (k : Rates n) (ET FT ST : ℝ) (u : Fin (2*n-1) → CoordinateSpace n) : Prop :=
  RationalRates k ∧ RationalReal ET ∧ RationalReal FT ∧ RationalReal ST ∧
  k.Positive ∧ 0 < ET ∧ 0 < FT ∧ 0 < ST ∧ Function.Injective u ∧
    (∀ j, RationalState (unChart ET FT ST (ofCoordinateSpace (u j))) ∧
      (unChart ET FT ST (ofCoordinateSpace (u j))).Positive ∧
      restrictedFieldEuclid ET FT ST k (u j) = 0) ∧
    (∀ i : Fin n, ∃ j : Fin (2*n-1), j.val = 2*i.val ∧
      IsLinearlyStable ET FT ST k (u j) ∧
      IsLocallyAsymptoticallyStableClass ET FT ST k (u j)) ∧
    (∀ j : Fin (2*n-1), Odd j.val → IsOneUnstableSaddle ET FT ST k (u j)) ∧
    {x : State n | x.Positive ∧ Equilibrium k x ∧ InClass ET FT ST x} =
      Set.range (fun j : Fin (2*n-1) => unChart ET FT ST (ofCoordinateSpace (u j))) ∧
    {x : State n | x.Positive ∧ Equilibrium k x ∧ InClass ET FT ST x}.ncard = 2*n-1

/-- Every odd saddle in a supplied common physical family has an actual
positive analytic unstable curve for these same rates and totals. -/
theorem paper_full_configuration_odd_positive_unstable_curves
    {n : ℕ} (k : Rates n) (ET FT ST : ℝ)
    (u : Fin (2*n-1) → CoordinateSpace n)
    (hstates : ∀ j, (unChart ET FT ST (ofCoordinateSpace (u j))).Positive ∧
      restrictedFieldEuclid ET FT ST k (u j) = 0)
    (hsaddles : ∀ j : Fin (2*n-1), Odd j.val → IsOneUnstableSaddle ET FT ST k (u j)) :
    ∀ j : Fin (2*n-1), Odd j.val →
      ActualPositiveAnalyticUnstableCurveAt ET FT ST k (u j) := by
  intro j hj
  exact actual_positive_saddle_analytic_unstable_curve ET FT ST k (u j)
    (hstates j).1 (hstates j).2 (hsaddles j hj)

/-- For every positive chain length one common rational system has its exact
full sink/saddle configuration and an actual positive analytic unstable curve
at every odd-index saddle. No independently chosen system is conjoined. -/
theorem all_positive_sizes_rational_full_configuration_with_positive_unstable_curves
    (n : ℕ) (hn : 1 ≤ n) :
    ∃ (k : Rates n) (ET FT ST : ℝ) (u : Fin (2*n-1) → CoordinateSpace n),
      PaperRationalFullConfigurationAt k ET FT ST u ∧
      ∀ j : Fin (2*n-1), Odd j.val →
        ActualPositiveAnalyticUnstableCurveAt ET FT ST k (u j) := by
  obtain ⟨k, ET, FT, ST, u, hkr, hETr, hFTr, hSTr, hk, hET, hFT, hST,
    hinj, hstates, hsinks, hsaddles, hexact, hcard⟩ :=
    all_positive_sizes_rational_full_family_with_sinks_and_saddles n hn
  refine ⟨k, ET, FT, ST, u, ?_, ?_⟩
  · exact ⟨hkr, hETr, hFTr, hSTr, hk, hET, hFT, hST, hinj,
      hstates, hsinks, hsaddles, hexact, hcard⟩
  · exact paper_full_configuration_odd_positive_unstable_curves k ET FT ST u
      (fun j => ⟨(hstates j).2.1, (hstates j).2.2⟩) hsaddles

end
end PhosphorylationStableCapacity
