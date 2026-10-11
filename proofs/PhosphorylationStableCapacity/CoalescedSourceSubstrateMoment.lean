module
public import proofs.PhosphorylationStableCapacity.CoalescedLiteralFeedbackMoments

@[expose] public section

namespace PhosphorylationStableCapacity

open Polynomial PhosphorylationSharpness Filter

noncomputable section

/-- The literal source free-substrate concentration is the coefficient of
the converted inventory polynomial, with the same normalization as both
complex species. -/
theorem coalescedFiniteState_S_coeff (m : ℕ) (r : ℝ)
    (i : Fin (m + 3)) :
    (coalescedFiniteState (m + 1) r).S i =
      ((1 + X) * coalescedRawD (m + 1) r).coeff i.val /
        (coalescedRawD (m + 1) r).eval 1 := by
  norm_num [coalescedFiniteState, reconstruct, ratio,
    rootS_three, rootF, div_eq_mul_inv]

/-- The free-substrate first level moment is the derivative of its
inventory polynomial, normalized by the source value. -/
theorem coalescedFiniteState_S_firstMoment (m : ℕ) (r : ℝ)
    (hdeg : ((1 + X) * coalescedRawD (m + 1) r).natDegree ≤ m + 2) :
    (∑ i : Fin (m + 3),
      (coalescedFiniteState (m + 1) r).S i * (i.val : ℝ)) =
      (derivative ((1 + X) * coalescedRawD (m + 1) r)).eval 1 /
        (coalescedRawD (m + 1) r).eval 1 := by
  simp_rw [coalescedFiniteState_S_coeff, div_mul_eq_mul_div]
  rw [← Finset.sum_div]
  have hsum :
      (∑ i : Fin (m + 3),
        ((1 + X) * coalescedRawD (m + 1) r).coeff i.val *
          (i.val : ℝ)) =
      (derivative ((1 + X) * coalescedRawD (m + 1) r)).eval 1 := by
    calc
      _ = ∑ j ∈ Finset.range (m + 3),
          ((1 + X) * coalescedRawD (m + 1) r).coeff j *
            (j : ℝ) :=
        Fin.sum_univ_eq_sum_range _ _
      _ = _ := (derivative_eval_one_eq_coeff_moment _ (m + 2) hdeg).symm
  rw [hsum]

theorem coalescedInventory_deriv_eval_one (m : ℕ) (r : ℝ) :
    (derivative ((1 + X) * coalescedRawD (m + 1) r)).eval 1 =
      (coalescedRawD (m + 1) r).eval 1 +
        2 * (derivative (coalescedRawD (m + 1) r)).eval 1 := by
  norm_num [derivative_mul, derivative_add]

/-- The free-substrate first moment has the explicit finite source formula
for all sufficiently large positive source parameters. -/
theorem coalescedFiniteState_S_firstMoment_eventually (m : ℕ) :
    ∀ᶠ r : ℝ in atTop,
      (∑ i : Fin (m + 3),
        (coalescedFiniteState (m + 1) r).S i * (i.val : ℝ)) =
          ((coalescedRawD (m + 1) r).eval 1 +
            2 * (derivative (coalescedRawD (m + 1) r)).eval 1) /
              (coalescedRawD (m + 1) r).eval 1 := by
  have hsource := conversion_eventually_positive
    (coalescedPair_dense (m + 1)).1
    (coalescedPair_dense (m + 1)).2
  filter_upwards [hsource] with r hpositive
  have hlin : (1 + X : ℝ[X]).natDegree ≤ 1 := by
    calc
      _ ≤ max (1 : ℝ[X]).natDegree X.natDegree :=
        Polynomial.natDegree_add_le _ _
      _ = 1 := by simp [Polynomial.natDegree_X]
  have hD : (coalescedRawD (m + 1) r).natDegree ≤ m + 1 :=
    Polynomial.natDegree_le_iff_coeff_eq_zero.mpr hpositive.1.2
  have hdegree : ((1 + X) * coalescedRawD (m + 1) r).natDegree ≤
      m + 2 := by
    calc
      _ ≤ (1 + X : ℝ[X]).natDegree +
          (coalescedRawD (m + 1) r).natDegree :=
        Polynomial.natDegree_mul_le
      _ ≤ m + 2 := by omega
  rw [coalescedFiniteState_S_firstMoment m r hdegree,
    coalescedInventory_deriv_eval_one]

end
end PhosphorylationStableCapacity
