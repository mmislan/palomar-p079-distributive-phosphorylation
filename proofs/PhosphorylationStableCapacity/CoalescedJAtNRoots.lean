module
public import proofs.PhosphorylationStableCapacity.CoalescedChebyshevAllRoots

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section

/-- The second component of the literal recurrence can be recovered from two
successive numerator values. -/
theorem coalescedJ_from_N (m : ℕ) (u : ℝ) :
    12 * (coalescedPair m).2.eval u =
      (coalescedPair (m + 1)).1.eval u -
        (16 + 8 * u) * (coalescedPair m).1.eval u := by
  have hN : (coalescedPair (m + 1)).1.eval u =
      (16 + 8 * u) * (coalescedPair m).1.eval u +
        12 * (coalescedPair m).2.eval u := by
    change (PhosphorylationSharpness.nextN 3 3
      (coalescedPair m).1 (coalescedPair m).2).eval u = _
    exact nextN_33_eval _ _ u
  linarith

theorem coalescedJ_at_N_root (m j : ℕ) (hj : j < m) :
    12 * (coalescedPair m).2.eval (coalescedRoot m j) =
      (coalescedPair (m + 1)).1.eval (coalescedRoot m j) := by
  rw [coalescedJ_from_N, coalescedN_eval_root m j hj]
  ring

end
end PhosphorylationStableCapacity
