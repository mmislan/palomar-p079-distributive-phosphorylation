module
public import proofs.PhosphorylationStableCapacity.CoalescedAffineZeroMode

@[expose] public section

namespace PhosphorylationStableCapacity

open Filter

noncomputable section

/-- The affine tangent has zero total loaded-level derivative at the
literal source, using the exact finite mass matrix and its verified row
moments. -/
theorem coalescedAffineZeroTangent_eventually_mass_total_zero (m : ℕ) :
    ∀ᶠ r : ℝ in atTop,
      (∑ i : Fin (m + 3),
        (coalescedFullMass m r).mulVec
          (coalescedAffineZeroTangent m r) i) = 0 := by
  filter_upwards [coalescedLiteralMassMoments_eventually m,
    coalescedSourceMomentDet_eventually_zero m,
    coalescedFiniteState_eventually_component_totals (m + 1),
    eventually_gt_atTop (0 : ℝ)] with r hmoment hdet htot hr
  let σ := coalescedAffineZeroTangent m r
  have htotal := coalescedFullMass_total_action m r σ
    (ne_of_gt hr) htot.1 htot.2.1
  rw [htotal]
  have hmass :
      (∑ k : Fin (m + 3),
        (coalescedFiniteState (m + 1) r).S k * σ k) +
          (∑ k : Fin (m + 3),
            coalescedFiniteCLevel m r k * σ k) / (2 * r) +
          (∑ k : Fin (m + 3),
            coalescedFiniteYLevel m r k * σ k) / 2 =
      (∑ k : Fin (m + 3),
        coalescedLiteralMassTotalWeight m r k * σ k) := by
    unfold coalescedLiteralMassTotalWeight
    simp_rw [add_mul, div_mul_eq_mul_div]
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
      ← Finset.sum_div, ← Finset.sum_div]
  rw [hmass]
  change (∑ k : Fin (m + 3),
    coalescedLiteralMassTotalWeight m r k *
      ((1 - coalescedSourceH1 m r) +
        coalescedSourceH0 r * (k.val : ℝ))) = 0
  rw [affine_weighted_sum, hmoment.1, hmoment.2]
  nlinarith [hdet]

end
end PhosphorylationStableCapacity
