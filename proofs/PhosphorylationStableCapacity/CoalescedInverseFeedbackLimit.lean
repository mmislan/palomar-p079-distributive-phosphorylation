module
public import proofs.PhosphorylationStableCapacity.CoalescedInverseFeedbackWeights

@[expose] public section

namespace PhosphorylationStableCapacity

open Filter
open scoped Topology

noncomputable section

/-- The literal common feedback appearing in the reduced catalytic-current
derivative, evaluated on the scaled finite inverse response. -/
def coalescedInverseFeedback (m : ℕ) (r : ℝ)
    (q : Fin (m + 3) → ℝ) : ℝ :=
  ∑ j : Fin (m + 3),
    (coalescedFiniteYLevel m r j / 2 -
      coalescedFiniteCLevel m r j / (2 * r)) *
        coalescedInverseResponse m r q j

/-- The actual source feedback converges to the explicit mode feedback,
which equals the manuscript's formula (7). -/
theorem coalescedInverseFeedback_explicit_limit (m : ℕ)
    (q : Fin (m + 3) → ℝ)
    (hqsum : (∑ j : Fin (m + 3), q j) = 0)
    (hqlast : q (Fin.last (m + 2)) = 0) :
    ∃ a b : ℝ,
      Tendsto (fun r : ℝ => coalescedInverseFeedback m r q) atTop
        (𝓝 (2 * b - a)) ∧
      2 * b - a =
        (10 * coalescedInverseT m q +
          (2 + coalescedV m) * coalescedInverseU m q) /
            (2 * (7 - 4 * coalescedV m)) := by
  obtain ⟨a, b, hresponse, hrow, hlast, hfeedback⟩ :=
    coalescedInverseResponse_explicit_mode_limit m q hqsum hqlast
  let τ := coalescedInverseParticular m q +
    coalescedFullKernelVector m a b
  have hlimit : Tendsto (fun r : ℝ => coalescedInverseFeedback m r q)
      atTop (𝓝 (∑ j : Fin (m + 3),
        (coalescedFullYLimit m j / 2 -
          coalescedFullLevelWeight m j / 2) * τ j)) := by
    unfold coalescedInverseFeedback
    apply tendsto_finsetSum
    intro j hj
    have hY := coalescedFiniteYLevel_tendsto_full_limit m j
    have hC := coalescedFiniteCLevel_scaled_tendsto m j
    have hCshare : Tendsto
        (fun r : ℝ => coalescedFiniteCLevel m r j / (2 * r)) atTop
        (𝓝 (coalescedFullLevelWeight m j / 2)) := by
      apply (hC.div_const 2).congr'
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with r hr
      field_simp [ne_of_gt hr]
    have hτ : Tendsto (fun r : ℝ => coalescedInverseResponse m r q j)
        atTop (𝓝 (τ j)) := by
      exact (tendsto_pi_nhds.mp hresponse) j
    exact ((hY.div_const 2).sub hCshare).mul hτ
  have hstatic :
      (∑ j : Fin (m + 3),
        (coalescedFullYLimit m j / 2 -
          coalescedFullLevelWeight m j / 2) * τ j) = 2 * b - a := by
    calc
      _ = (∑ j : Fin (m + 3), coalescedFullYLimit m j * τ j) / 2 -
          (∑ j : Fin (m + 3), coalescedFullLevelWeight m j * τ j) / 2 := by
            simp_rw [sub_mul, div_mul_eq_mul_div]
            rw [Finset.sum_sub_distrib, ← Finset.sum_div, ← Finset.sum_div]
      _ = 2 * b - a := coalescedInverseModeVector_feedback
        m q a b hqsum hqlast hlast
  rw [hstatic] at hlimit
  exact ⟨a, b, hlimit, hfeedback⟩

end
end PhosphorylationStableCapacity
