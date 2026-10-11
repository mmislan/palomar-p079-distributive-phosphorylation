module
public import proofs.PhosphorylationStableCapacity.CoalescedInverseFeedbackLimit
public import proofs.PhosphorylationStableCapacity.CoalescedCurrentDerivative

@[expose] public section

namespace PhosphorylationStableCapacity

open Filter
open scoped Topology

noncomputable section

/-- The finite feedback used in the inverse-limit proof is exactly the
common global term in the literal catalytic-current derivative. -/
theorem coalescedInverseFeedback_eq_current_form (m : ℕ) (r : ℝ)
    (q : Fin (m + 3) → ℝ) :
    coalescedInverseFeedback m r q =
      (∑ j : Fin (m + 3), coalescedFiniteYLevel m r j *
        coalescedInverseResponse m r q j) / 2 -
      (∑ j : Fin (m + 3), coalescedFiniteCLevel m r j *
        coalescedInverseResponse m r q j) / (2 * r) := by
  unfold coalescedInverseFeedback
  simp_rw [sub_mul]
  rw [Finset.sum_sub_distrib]
  congr 1
  · calc
      _ = ∑ j : Fin (m + 3),
          (coalescedFiniteYLevel m r j *
            coalescedInverseResponse m r q j) / 2 := by
              apply Finset.sum_congr rfl
              intro j _
              ring
      _ = _ := by rw [Finset.sum_div]
  · calc
      _ = ∑ j : Fin (m + 3),
          (coalescedFiniteCLevel m r j *
            coalescedInverseResponse m r q j) / (2 * r) := by
              apply Finset.sum_congr rfl
              intro j _
              ring
      _ = _ := by rw [Finset.sum_div]

/-- The actual finite feedback has a unique explicit scalar limit, free of
the auxiliary constants used to describe the limiting mode vector. -/
theorem coalescedInverseFeedback_tendsto_formula (m : ℕ)
    (q : Fin (m + 3) → ℝ)
    (hqsum : (∑ j : Fin (m + 3), q j) = 0)
    (hqlast : q (Fin.last (m + 2)) = 0) :
    Tendsto (fun r : ℝ => coalescedInverseFeedback m r q) atTop
      (𝓝 ((10 * coalescedInverseT m q +
          (2 + coalescedV m) * coalescedInverseU m q) /
            (2 * (7 - 4 * coalescedV m)))) := by
  obtain ⟨a, b, hlim, hformula⟩ :=
    coalescedInverseFeedback_explicit_limit m q hqsum hqlast
  rw [hformula] at hlim
  exact hlim

end
end PhosphorylationStableCapacity
