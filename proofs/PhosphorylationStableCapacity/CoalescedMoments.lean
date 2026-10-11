module
public import proofs.PhosphorylationSharpness.PublicationAlgebra

@[expose] public section

namespace PhosphorylationStableCapacity

open PhosphorylationSharpness Polynomial

noncomputable section

/-- The inherited positive-pair recurrence specialized to repeated roots
`(3,3)`. Its source equality is established below. -/
def coalescedPair : ℕ → ℝ[X] × ℝ[X]
  | 0 => (1, 1)
  | m + 1 =>
      let pq := coalescedPair m
      (nextN 3 3 pq.1 pq.2, nextJ 3 3 pq.1 pq.2)

theorem coalescedPair_eq_source (m : ℕ) :
    coalescedPair m = prescribedPair 3 (List.replicate m (3, 3)) := by
  induction m with
  | zero => norm_num [coalescedPair, prescribedPair]
  | succ m ih =>
      simp [coalescedPair, prescribedPair, List.replicate_succ, ih]

theorem nextN_33_eval_one (p q : ℝ[X]) :
    (nextN 3 3 p q).eval 1 = 24 * p.eval 1 + 12 * q.eval 1 := by
  simp [nextN]
  ring

theorem nextJ_33_eval_one (p q : ℝ[X]) :
    (nextJ 3 3 p q).eval 1 = 24 * p.eval 1 + 12 * q.eval 1 := by
  simp [nextJ]
  ring

/-- Exact all-size values of both source polynomials at the coalesced point. -/
theorem coalescedPair_eval_one (m : ℕ) :
    (coalescedPair m).1.eval 1 = (36 : ℝ)^m ∧
      (coalescedPair m).2.eval 1 = (36 : ℝ)^m := by
  induction m with
  | zero => simp [coalescedPair]
  | succ m ih =>
      constructor
      · change (nextN 3 3 (coalescedPair m).1 (coalescedPair m).2).eval 1 = _
        rw [nextN_33_eval_one, ih.1, ih.2, pow_succ]
        ring
      · change (nextJ 3 3 (coalescedPair m).1 (coalescedPair m).2).eval 1 = _
        rw [nextJ_33_eval_one, ih.1, ih.2, pow_succ]
        ring

end
end PhosphorylationStableCapacity
