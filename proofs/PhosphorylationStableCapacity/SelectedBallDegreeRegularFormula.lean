module
public import proofs.PhosphorylationStableCapacity.SelectedBallSignedSum

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section
attribute [local instance] Classical.propDecidable
open PhosphorylationSharpness

/-- Conditional on a genuine closed-ball degree, the regular-zero
formula equals the exact P079 signed local equilibrium sum. -/
theorem selected_ball_signed_sum_eq_degree_of_regular {n : ℕ}
    (ET FT ST : ℝ) (k : Rates n)
    (x : CoordinateSpace n) (r : ℝ)
    (hinside : Metric.closedBall x r ⊆
      classPolytopeStrict n ET FT ST)
    (E : Set (State n))
    (hE : E = {z | z.Positive ∧ Equilibrium k z ∧ InClass ET FT ST z})
    (hfinite : E.Finite)
    (hregular : ∀ z ∈ E,
      (restrictedJacobianMatrix ET FT ST k
        (toCoordinateSpace (chart z))).det ≠ 0)
    (hboundary : ∀ y : CoordinateSpace n, dist y x = r →
      restrictedFieldEuclid ET FT ST k y ≠ 0)
    (D : ClosedBallDegree n x r) :
    (∑ z ∈ hfinite.toFinset.filter
      (fun z => toCoordinateSpace (chart z) ∈ Metric.closedBall x r),
      signedNegativeFieldIndex ET FT ST k z) =
      D.degree (fun y : Metric.closedBall x r =>
        -restrictedFieldEuclid ET FT ST k y.1) := by
  let Zs : Set (Metric.closedBall x r) :=
    {y | restrictedFieldEuclid ET FT ST k y.1 = 0}
  have hZfinite : Zs.Finite :=
    finite_selected_ball_zeros ET FT ST k x r hinside E hE hfinite
  let Z : Finset (Metric.closedBall x r) := hZfinite.toFinset
  have hZ : ∀ y : Metric.closedBall x r,
      y ∈ Z ↔ restrictedFieldEuclid ET FT ST k y.1 = 0 := by
    intro y
    exact hZfinite.mem_toFinset
  have hsum := selected_ball_signed_sum_eq_zero_sum
    ET FT ST k x r hinside E hE hfinite Z hZ
  have hdeg := D.regular_zero_sum
    (fun u => -restrictedFieldEuclid ET FT ST k u)
    (differentiable_restrictedFieldEuclid ET FT ST k).neg
    Z
    (by
      intro y
      simpa only [neg_eq_zero] using (hZ y).symm)
    (by
      intro y hy
      exact neg_ne_zero.mpr (hboundary y.1 hy))
    (by
      intro y hy
      let z := unChart ET FT ST (ofCoordinateSpace y.1)
      have hyzero : restrictedFieldEuclid ET FT ST k y.1 = 0 :=
        (hZ y).mp hy
      have hprops := (selected_ball_zero_iff_positive_equilibrium
        ET FT ST k x r hinside y).mp hyzero
      have hzE : z ∈ E := by
        rw [hE]
        exact hprops
      have hchart : toCoordinateSpace (chart z) = y.1 := by
        simp only [z, chart_unChart, to_ofCoordinateSpace]
      have hreg := hregular z hzE
      rw [hchart] at hreg
      simpa only [negative_restricted_field_derivative_det_eq,
        Matrix.det_neg] using
        mul_ne_zero (pow_ne_zero _ (by norm_num : (-1 : ℝ) ≠ 0)) hreg)
  exact hsum.trans hdeg.symm

end
end PhosphorylationStableCapacity
