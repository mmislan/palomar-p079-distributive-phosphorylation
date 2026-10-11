module
public import proofs.PhosphorylationStableCapacity.SelectedBallZeroFinite

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section
attribute [local instance] Classical.propDecidable
open PhosphorylationSharpness

/-- Reindex the P079 local signed sum over positive physical
equilibria as the generic regular-zero determinant sum on the selected
closed coordinate ball. -/
theorem selected_ball_signed_sum_eq_zero_sum {n : ℕ}
    (ET FT ST : ℝ) (k : Rates n)
    (x : CoordinateSpace n) (r : ℝ)
    (hinside : Metric.closedBall x r ⊆
      classPolytopeStrict n ET FT ST)
    (E : Set (State n))
    (hE : E = {z | z.Positive ∧ Equilibrium k z ∧ InClass ET FT ST z})
    (hfinite : E.Finite)
    (Z : Finset (Metric.closedBall x r))
    (hZ : ∀ y : Metric.closedBall x r,
      y ∈ Z ↔ restrictedFieldEuclid ET FT ST k y.1 = 0) :
    (∑ z ∈ hfinite.toFinset.filter
      (fun z => toCoordinateSpace (chart z) ∈ Metric.closedBall x r),
      signedNegativeFieldIndex ET FT ST k z) =
    ∑ y ∈ Z,
      if 0 < LinearMap.det
        (fderiv ℝ (fun u => -restrictedFieldEuclid ET FT ST k u)
          y.1).toLinearMap
      then (1 : ℤ) else -1 := by
  classical
  apply Finset.sum_bij (fun z hz =>
    (⟨toCoordinateSpace (chart z), (Finset.mem_filter.mp hz).2⟩ :
      Metric.closedBall x r))
  · intro z hz
    have hzE : z ∈ E := by
      exact hfinite.mem_toFinset.mp (Finset.mem_filter.mp hz).1
    have hprops : z.Positive ∧ Equilibrium k z ∧ InClass ET FT ST z := by
      rw [hE] at hzE
      exact hzE
    apply (hZ _).2
    apply (restrictedFieldEuclid_eq_zero_iff ET FT ST k _).2
    simpa only [of_toCoordinateSpace,
      unChart_chart_of_inClass ET FT ST z hprops.2.2] using hprops.2.1
  · intro z₁ hz₁ z₂ hz₂ heq
    have hcoord : toCoordinateSpace (chart z₁) =
        toCoordinateSpace (chart z₂) := congrArg Subtype.val heq
    have hchart : chart z₁ = chart z₂ := by
      have h := congrArg ofCoordinateSpace hcoord
      simpa only [of_toCoordinateSpace] using h
    have hz₁E : z₁ ∈ E :=
      hfinite.mem_toFinset.mp (Finset.mem_filter.mp hz₁).1
    have hz₂E : z₂ ∈ E :=
      hfinite.mem_toFinset.mp (Finset.mem_filter.mp hz₂).1
    rw [hE] at hz₁E hz₂E
    calc
      z₁ = unChart ET FT ST (chart z₁) :=
        (unChart_chart_of_inClass ET FT ST z₁ hz₁E.2.2).symm
      _ = unChart ET FT ST (chart z₂) := congrArg _ hchart
      _ = z₂ := unChart_chart_of_inClass ET FT ST z₂ hz₂E.2.2
  · intro y hy
    let z := unChart ET FT ST (ofCoordinateSpace y.1)
    have hzero : restrictedFieldEuclid ET FT ST k y.1 = 0 :=
      (hZ y).1 hy
    have hprops := (selected_ball_zero_iff_positive_equilibrium
      ET FT ST k x r hinside y).1 hzero
    have hzE : z ∈ E := by
      rw [hE]
      exact hprops
    have hchart : toCoordinateSpace (chart z) = y.1 := by
      simp only [z, chart_unChart, to_ofCoordinateSpace]
    have hzS : z ∈ hfinite.toFinset.filter
        (fun z => toCoordinateSpace (chart z) ∈ Metric.closedBall x r) := by
      apply Finset.mem_filter.mpr
      constructor
      · exact hfinite.mem_toFinset.mpr hzE
      · simpa only [hchart] using y.2
    refine ⟨z, hzS, ?_⟩
    exact Subtype.ext hchart
  · intro z hz
    exact signedNegativeFieldIndex_eq_derivative_sign ET FT ST k z

end
end PhosphorylationStableCapacity
