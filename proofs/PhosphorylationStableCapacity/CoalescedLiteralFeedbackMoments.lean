module
public import proofs.PhosphorylationStableCapacity.CoalescedOccupiedFirstMoments
public import proofs.PhosphorylationStableCapacity.CoalescedBindingDerivative

@[expose] public section

namespace PhosphorylationStableCapacity

open Polynomial Filter PhosphorylationSharpness

noncomputable section

/-- The common literal current-feedback weight at each occupied level. -/
def coalescedLiteralFeedbackWeight (m : ℕ) (r : ℝ)
    (k : Fin (m + 3)) : ℝ :=
  coalescedFiniteYLevel m r k / 2 -
    coalescedFiniteCLevel m r k / (2 * r)

theorem coalescedLiteralFeedback_H0 (m : ℕ) (r : ℝ)
    (hr : r ≠ 0)
    (hC : (∑ i : Fin (m + 2),
      (coalescedFiniteState (m + 1) r).C i) = 2 * r - 1)
    (hD : (∑ i : Fin (m + 2),
      (coalescedFiniteState (m + 1) r).D i) = 1) :
    (∑ k : Fin (m + 3), coalescedLiteralFeedbackWeight m r k) =
      coalescedSourceH0 r := by
  unfold coalescedLiteralFeedbackWeight coalescedSourceH0
  rw [Finset.sum_sub_distrib, ← Finset.sum_div, ← Finset.sum_div]
  rw [coalescedFiniteYLevel_sum, coalescedFiniteCLevel_sum,
    hC, hD]
  field_simp [hr]
  ring

theorem coalescedLiteralFeedback_H1 (m : ℕ) (r : ℝ)
    (hr : r ≠ 0)
    (hY : (∑ k : Fin (m + 3),
      coalescedFiniteYLevel m r k * (k.val : ℝ)) =
        ((coalescedRawD (m + 1) r).eval 1 +
          (derivative (coalescedRawD (m + 1) r)).eval 1) /
            (coalescedRawD (m + 1) r).eval 1)
    (hC : (∑ k : Fin (m + 3),
      coalescedFiniteCLevel m r k * (k.val : ℝ)) =
        (derivative (coalescedRawB (m + 1) r)).eval 1 /
          (coalescedRawD (m + 1) r).eval 1) :
    (∑ k : Fin (m + 3),
      coalescedLiteralFeedbackWeight m r k * (k.val : ℝ)) =
        coalescedSourceH1 m r := by
  unfold coalescedLiteralFeedbackWeight coalescedSourceH1
  simp_rw [sub_mul, div_mul_eq_mul_div]
  rw [Finset.sum_sub_distrib, ← Finset.sum_div, ← Finset.sum_div,
    hY, hC]
  field_simp [hr]

/-- Both literal feedback moments equal the source scalar candidates for
all sufficiently large positive source parameters. -/
theorem coalescedLiteralFeedbackMoments_eventually (m : ℕ) :
    ∀ᶠ r : ℝ in atTop,
      (∑ k : Fin (m + 3), coalescedLiteralFeedbackWeight m r k) =
        coalescedSourceH0 r ∧
      (∑ k : Fin (m + 3),
        coalescedLiteralFeedbackWeight m r k * (k.val : ℝ)) =
          coalescedSourceH1 m r := by
  filter_upwards [coalescedFiniteState_eventually_component_totals (m + 1),
    coalescedOccupiedComplex_firstMoments_eventually m,
    eventually_gt_atTop (0 : ℝ)] with r htot hmoment hr
  exact ⟨coalescedLiteralFeedback_H0 m r (ne_of_gt hr)
    htot.1 htot.2.1,
    coalescedLiteralFeedback_H1 m r (ne_of_gt hr) hmoment.2 hmoment.1⟩

end
end PhosphorylationStableCapacity
