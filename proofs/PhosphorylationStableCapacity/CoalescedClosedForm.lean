module
public import proofs.PhosphorylationStableCapacity.CoalescedFeedbackSignReduction

@[expose] public section

namespace PhosphorylationStableCapacity

open PhosphorylationSharpness Polynomial

noncomputable section

def coalescedU (x : ℝ) : ℝ := (x ^ 2 - 1) / 8

theorem nextN_33_eval (p q : ℝ[X]) (u : ℝ) :
    (nextN 3 3 p q).eval u =
      (16 + 8 * u) * p.eval u + 12 * q.eval u := by
  simp [nextN]
  ring

theorem nextJ_33_eval (p q : ℝ[X]) (u : ℝ) :
    (nextJ 3 3 p q).eval u =
      (4 + 8 * u) * q.eval u + 24 * u * p.eval u := by
  simp [nextJ]
  ring

/-- Exact all-size closed form of the repeated `(3,3)` source under
`u=(x²-1)/8`. This is algebraic; root location and coefficient-ratio
monotonicity remain separate obligations. -/
theorem coalescedPair_closed_form (m : ℕ) (x : ℝ) :
    2 * x * (coalescedPair m).1.eval (coalescedU x) =
      (x + 3) ^ (2 * m + 1) + (x - 3) ^ (2 * m + 1) ∧
    4 * x * (coalescedPair m).2.eval (coalescedU x) =
      x * ((x + 3) ^ (2 * m + 1) - (x - 3) ^ (2 * m + 1)) -
        ((x + 3) ^ (2 * m + 1) + (x - 3) ^ (2 * m + 1)) := by
  induction m with
  | zero =>
      constructor
      · norm_num [coalescedPair]
        ring
      · norm_num [coalescedPair]
        ring
  | succ m ih =>
      have hk : 2 * (m + 1) + 1 = (2 * m + 1) + 2 := by omega
      constructor
      · change 2 * x * (nextN 3 3 (coalescedPair m).1
          (coalescedPair m).2).eval (coalescedU x) = _
        calc
          2 * x * (nextN 3 3 (coalescedPair m).1
              (coalescedPair m).2).eval (coalescedU x) =
            (x ^ 2 + 15) *
              (2 * x * (coalescedPair m).1.eval (coalescedU x)) +
            6 * (4 * x * (coalescedPair m).2.eval (coalescedU x)) := by
              rw [nextN_33_eval]
              dsimp [coalescedU]
              ring
          _ = _ := by
            rw [ih.1, ih.2, hk, pow_add, pow_add]
            ring
      · change 4 * x * (nextJ 3 3 (coalescedPair m).1
          (coalescedPair m).2).eval (coalescedU x) = _
        calc
          4 * x * (nextJ 3 3 (coalescedPair m).1
              (coalescedPair m).2).eval (coalescedU x) =
            6 * (x ^ 2 - 1) *
              (2 * x * (coalescedPair m).1.eval (coalescedU x)) +
            (x ^ 2 + 3) *
              (4 * x * (coalescedPair m).2.eval (coalescedU x)) := by
              rw [nextJ_33_eval]
              dsimp [coalescedU]
              ring
          _ = _ := by
            rw [ih.1, ih.2, hk, pow_add, pow_add]
            ring

end
end PhosphorylationStableCapacity
