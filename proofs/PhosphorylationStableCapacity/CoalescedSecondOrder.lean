module
public import proofs.PhosphorylationStableCapacity.CoalescedClosedForm

@[expose] public section

namespace PhosphorylationStableCapacity

open PhosphorylationSharpness Polynomial

noncomputable section

theorem coalescedN_eval_zero (u : ℝ) :
    (coalescedPair 0).1.eval u = 1 := by
  simp [coalescedPair]

theorem coalescedN_eval_one (u : ℝ) :
    (coalescedPair 1).1.eval u = 28 + 8 * u := by
  change (nextN 3 3 (1 : ℝ[X]) 1).eval u = _
  rw [nextN_33_eval]
  norm_num
  ring

/-- Cayley-Hamilton for the two-component repeated-root recurrence,
specialized to its first component. -/
theorem coalescedN_eval_add_two (m : ℕ) (u : ℝ) :
    (coalescedPair (m + 2)).1.eval u =
      (20 + 16 * u) * (coalescedPair (m + 1)).1.eval u -
        64 * (u - 1) ^ 2 * (coalescedPair m).1.eval u := by
  have hN1 :
      (coalescedPair (m + 1)).1.eval u =
        (16 + 8 * u) * (coalescedPair m).1.eval u +
          12 * (coalescedPair m).2.eval u := by
    change (nextN 3 3 (coalescedPair m).1 (coalescedPair m).2).eval u = _
    exact nextN_33_eval _ _ u
  have hJ1 :
      (coalescedPair (m + 1)).2.eval u =
        (4 + 8 * u) * (coalescedPair m).2.eval u +
          24 * u * (coalescedPair m).1.eval u := by
    change (nextJ 3 3 (coalescedPair m).1 (coalescedPair m).2).eval u = _
    exact nextJ_33_eval _ _ u
  calc
    (coalescedPair (m + 2)).1.eval u =
        (16 + 8 * u) * (coalescedPair (m + 1)).1.eval u +
          12 * (coalescedPair (m + 1)).2.eval u := by
      change (nextN 3 3 (coalescedPair (m + 1)).1
        (coalescedPair (m + 1)).2).eval u = _
      exact nextN_33_eval _ _ u
    _ = (20 + 16 * u) * (coalescedPair (m + 1)).1.eval u -
        64 * (u - 1) ^ 2 * (coalescedPair m).1.eval u := by
      rw [hN1, hJ1]
      ring

end
end PhosphorylationStableCapacity
