module
public import proofs.PhosphorylationStableCapacity.CoalescedSourceSubstrateMoment
public import proofs.PhosphorylationStableCapacity.CoalescedMassModeRows

@[expose] public section

namespace PhosphorylationStableCapacity

open Polynomial Filter PhosphorylationSharpness

noncomputable section

/-- The total-row coefficient of the exact finite loaded binding mass. -/
def coalescedLiteralMassTotalWeight (m : ℕ) (r : ℝ)
    (k : Fin (m + 3)) : ℝ :=
  (coalescedFiniteState (m + 1) r).S k +
    coalescedFiniteCLevel m r k / (2 * r) +
    coalescedFiniteYLevel m r k / 2

theorem coalescedLiteralMass_T0 (m : ℕ) (r : ℝ)
    (hr : r ≠ 0)
    (hC : (∑ i : Fin (m + 2),
      (coalescedFiniteState (m + 1) r).C i) = 2 * r - 1)
    (hD : (∑ i : Fin (m + 2),
      (coalescedFiniteState (m + 1) r).D i) = 1)
    (hS : (∑ i : Fin (m + 3),
      (coalescedFiniteState (m + 1) r).S i) = 2) :
    (∑ k : Fin (m + 3), coalescedLiteralMassTotalWeight m r k) =
      coalescedSourceT0 r := by
  unfold coalescedLiteralMassTotalWeight coalescedSourceT0
  simp_rw [Finset.sum_add_distrib]
  rw [← Finset.sum_div, ← Finset.sum_div,
    coalescedFiniteCLevel_sum, coalescedFiniteYLevel_sum,
    hC, hD, hS]
  field_simp [hr]
  ring

theorem coalescedLiteralMass_T1 (m : ℕ) (r : ℝ)
    (hr : r ≠ 0)
    (hD0 : (coalescedRawD (m + 1) r).eval 1 ≠ 0)
    (hS : (∑ k : Fin (m + 3),
      (coalescedFiniteState (m + 1) r).S k * (k.val : ℝ)) =
        ((coalescedRawD (m + 1) r).eval 1 +
          2 * (derivative (coalescedRawD (m + 1) r)).eval 1) /
            (coalescedRawD (m + 1) r).eval 1)
    (hC : (∑ k : Fin (m + 3),
      coalescedFiniteCLevel m r k * (k.val : ℝ)) =
        (derivative (coalescedRawB (m + 1) r)).eval 1 /
          (coalescedRawD (m + 1) r).eval 1)
    (hY : (∑ k : Fin (m + 3),
      coalescedFiniteYLevel m r k * (k.val : ℝ)) =
        ((coalescedRawD (m + 1) r).eval 1 +
          (derivative (coalescedRawD (m + 1) r)).eval 1) /
            (coalescedRawD (m + 1) r).eval 1) :
    (∑ k : Fin (m + 3),
      coalescedLiteralMassTotalWeight m r k * (k.val : ℝ)) =
        coalescedSourceT1 m r := by
  unfold coalescedLiteralMassTotalWeight coalescedSourceT1
  simp_rw [add_mul, div_mul_eq_mul_div]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
    ← Finset.sum_div, ← Finset.sum_div, hS, hC, hY]
  field_simp [hr, hD0]
  ring

/-- Both total-row moments of the literal loaded mass coincide with the
source scalar candidates for all sufficiently large positive parameters. -/
theorem coalescedLiteralMassMoments_eventually (m : ℕ) :
    ∀ᶠ r : ℝ in atTop,
      (∑ k : Fin (m + 3), coalescedLiteralMassTotalWeight m r k) =
        coalescedSourceT0 r ∧
      (∑ k : Fin (m + 3),
        coalescedLiteralMassTotalWeight m r k * (k.val : ℝ)) =
          coalescedSourceT1 m r := by
  have hsource := conversion_eventually_positive
    (coalescedPair_dense (m + 1)).1
    (coalescedPair_dense (m + 1)).2
  filter_upwards [coalescedFiniteState_eventually_component_totals (m + 1),
    coalescedFiniteState_S_firstMoment_eventually m,
    coalescedOccupiedComplex_firstMoments_eventually m,
    hsource, eventually_gt_atTop (0 : ℝ)]
    with r htot hS hcomplex hpositive hr
  have hD0 : (coalescedRawD (m + 1) r).eval 1 ≠ 0 :=
    ne_of_gt (hpositive.1.eval_pos (by norm_num))
  exact ⟨coalescedLiteralMass_T0 m r (ne_of_gt hr)
      htot.1 htot.2.1 htot.2.2,
    coalescedLiteralMass_T1 m r (ne_of_gt hr) hD0
      hS hcomplex.1 hcomplex.2⟩

end
end PhosphorylationStableCapacity
