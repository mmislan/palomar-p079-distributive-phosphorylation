module
public import proofs.PhosphorylationStableCapacity.CoalescedSourceComplexCoefficients
public import proofs.PhosphorylationStableCapacity.CoalescedFiniteModeBlock

@[expose] public section

namespace PhosphorylationStableCapacity

open Polynomial Filter PhosphorylationSharpness

noncomputable section

/-- The kinase complex occupies its own substrate level; the extension by
zero at the final level does not change its first moment. -/
theorem coalescedFiniteCLevel_firstMoment_eq (m : ℕ) (r : ℝ) :
    (∑ k : Fin (m + 3),
      coalescedFiniteCLevel m r k * (k.val : ℝ)) =
    (∑ i : Fin (m + 2),
      (coalescedFiniteState (m + 1) r).C i * (i.val : ℝ)) := by
  rw [Fin.sum_univ_castSucc]
  simp [coalescedFiniteCLevel, Fin.val_last]

/-- The phosphatase complex for reaction i occupies substrate level i+1.
This is the exact finite shift of its first moment. -/
theorem coalescedFiniteYLevel_firstMoment_eq (m : ℕ) (r : ℝ) :
    (∑ k : Fin (m + 3),
      coalescedFiniteYLevel m r k * (k.val : ℝ)) =
    (∑ i : Fin (m + 2),
      (coalescedFiniteState (m + 1) r).D i * ((i.val : ℝ) + 1)) := by
  rw [Fin.sum_univ_succ]
  simp [coalescedFiniteYLevel, Fin.val_succ]

/-- The actual occupied complex-level moments are exactly the normalized
source derivatives, with the phosphatase shift included. -/
theorem coalescedOccupiedComplex_firstMoments_eventually (m : ℕ) :
    ∀ᶠ r : ℝ in atTop,
      (∑ k : Fin (m + 3),
        coalescedFiniteCLevel m r k * (k.val : ℝ)) =
          (derivative (coalescedRawB (m + 1) r)).eval 1 /
            (coalescedRawD (m + 1) r).eval 1 ∧
      (∑ k : Fin (m + 3),
        coalescedFiniteYLevel m r k * (k.val : ℝ)) =
          ((coalescedRawD (m + 1) r).eval 1 +
            (derivative (coalescedRawD (m + 1) r)).eval 1) /
              (coalescedRawD (m + 1) r).eval 1 := by
  have hsource := conversion_eventually_positive
    (coalescedPair_dense (m + 1)).1
    (coalescedPair_dense (m + 1)).2
  filter_upwards [coalescedFiniteState_firstMoments_eventually m,
    coalescedFiniteState_eventually_component_totals (m + 1), hsource]
    with r hmoment htot hpositive
  constructor
  · rw [coalescedFiniteCLevel_firstMoment_eq]
    exact hmoment.1
  · rw [coalescedFiniteYLevel_firstMoment_eq]
    simp_rw [mul_add]
    rw [Finset.sum_add_distrib]
    simp only [mul_one]
    rw [hmoment.2, htot.2.1]
    have hD : (coalescedRawD (m + 1) r).eval 1 ≠ 0 :=
      ne_of_gt (hpositive.1.eval_pos (by norm_num))
    field_simp [hD]
    ring

end
end PhosphorylationStableCapacity
