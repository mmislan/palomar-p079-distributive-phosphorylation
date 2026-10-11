module
public import proofs.PhosphorylationStableCapacity.CoalescedSourceFirstMoment
public import proofs.PhosphorylationStableCapacity.CoalescedFullMassLimit

@[expose] public section

namespace PhosphorylationStableCapacity

open Polynomial PhosphorylationSharpness Filter

noncomputable section

/-- The literal coalesced kinase complex is its converted source
coefficient divided by the common source normalization. -/
theorem coalescedFiniteState_C_coeff (m : ℕ) (r : ℝ)
    (i : Fin (m + 2)) :
    (coalescedFiniteState (m + 1) r).C i =
      (coalescedRawB (m + 1) r).coeff i.val /
        (coalescedRawD (m + 1) r).eval 1 := by
  norm_num [coalescedFiniteState, reconstruct, ratio,
    rootS_three, rootF, div_eq_mul_inv]

/-- The literal coalesced phosphatase complex is its converted source
coefficient divided by the same normalization. -/
theorem coalescedFiniteState_D_coeff (m : ℕ) (r : ℝ)
    (i : Fin (m + 2)) :
    (coalescedFiniteState (m + 1) r).D i =
      (coalescedRawD (m + 1) r).coeff i.val /
        (coalescedRawD (m + 1) r).eval 1 := by
  norm_num [coalescedFiniteState, reconstruct, ratio,
    rootS_three, rootF, div_eq_mul_inv]

/-- The literal kinase-complex first level moment is the source polynomial
derivative at one, normalized by the phosphatase source value. -/
theorem coalescedFiniteState_C_firstMoment (m : ℕ) (r : ℝ)
    (hdeg : (coalescedRawB (m + 1) r).natDegree ≤ m + 1) :
    (∑ i : Fin (m + 2),
      (coalescedFiniteState (m + 1) r).C i * (i.val : ℝ)) =
      (derivative (coalescedRawB (m + 1) r)).eval 1 /
        (coalescedRawD (m + 1) r).eval 1 := by
  simp_rw [coalescedFiniteState_C_coeff, div_mul_eq_mul_div]
  rw [← Finset.sum_div]
  rw [Fin.sum_univ_eq_sum_range
    (fun j : ℕ => (coalescedRawB (m + 1) r).coeff j * (j : ℝ))
    (m + 2)]
  rw [← derivative_eval_one_eq_coeff_moment _ (m + 1) hdeg]

/-- The literal phosphatase-complex first level moment, before shifting
each complex from reaction index to its occupied substrate level. -/
theorem coalescedFiniteState_D_firstMoment (m : ℕ) (r : ℝ)
    (hdeg : (coalescedRawD (m + 1) r).natDegree ≤ m + 1) :
    (∑ i : Fin (m + 2),
      (coalescedFiniteState (m + 1) r).D i * (i.val : ℝ)) =
      (derivative (coalescedRawD (m + 1) r)).eval 1 /
        (coalescedRawD (m + 1) r).eval 1 := by
  simp_rw [coalescedFiniteState_D_coeff, div_mul_eq_mul_div]
  rw [← Finset.sum_div]
  rw [Fin.sum_univ_eq_sum_range
    (fun j : ℕ => (coalescedRawD (m + 1) r).coeff j * (j : ℝ))
    (m + 2)]
  rw [← derivative_eval_one_eq_coeff_moment _ (m + 1) hdeg]

/-- Both literal complex first moments have their source-polynomial
derivative formulas for all sufficiently large finite source parameters. -/
theorem coalescedFiniteState_firstMoments_eventually (m : ℕ) :
    ∀ᶠ r : ℝ in atTop,
      (∑ i : Fin (m + 2),
        (coalescedFiniteState (m + 1) r).C i * (i.val : ℝ)) =
          (derivative (coalescedRawB (m + 1) r)).eval 1 /
            (coalescedRawD (m + 1) r).eval 1 ∧
      (∑ i : Fin (m + 2),
        (coalescedFiniteState (m + 1) r).D i * (i.val : ℝ)) =
          (derivative (coalescedRawD (m + 1) r)).eval 1 /
            (coalescedRawD (m + 1) r).eval 1 := by
  have hsource := conversion_eventually_positive
    (coalescedPair_dense (m + 1)).1
    (coalescedPair_dense (m + 1)).2
  filter_upwards [hsource] with r hpositive
  have hdegD : (coalescedRawD (m + 1) r).natDegree ≤ m + 1 :=
    Polynomial.natDegree_le_iff_coeff_eq_zero.mpr hpositive.1.2
  have hdegB : (coalescedRawB (m + 1) r).natDegree ≤ m + 1 :=
    Polynomial.natDegree_le_iff_coeff_eq_zero.mpr hpositive.2.2
  exact ⟨coalescedFiniteState_C_firstMoment m r hdegB,
    coalescedFiniteState_D_firstMoment m r hdegD⟩

end
end PhosphorylationStableCapacity
