module
public import proofs.PhosphorylationStableCapacity.CoalescedCoefficientRatioFactor

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section

theorem coalescedJRoot_neg (m : ℕ) (j : Fin m) :
    coalescedJRoot m j < 0 := by
  have hu := (coalescedJRoot_bounds m j).2.1
  by_cases hj : j.val = 0
  · simpa only [hj, ↓reduceIte] using hu
  · simp only [hj, ↓reduceIte] at hu
    have hpred : j.val - 1 < m := by omega
    exact lt_trans hu (coalescedRoot_neg m (j.val - 1) hpred)

/-- Coordinatewise factor-magnitude matching implied by the strict
interlacing: each companion root is closer to zero than its paired numerator
root. -/
theorem coalescedFactor_magnitude_order (m : ℕ) (j : Fin m) :
    0 < -coalescedJRoot m j ∧
      -coalescedJRoot m j < -coalescedRoot m j.val := by
  have hjneg := coalescedJRoot_neg m j
  have hbound := (coalescedJRoot_bounds m j).1
  constructor <;> linarith

end
end PhosphorylationStableCapacity
