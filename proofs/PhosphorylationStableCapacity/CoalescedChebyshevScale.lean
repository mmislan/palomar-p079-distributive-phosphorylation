module
public import proofs.PhosphorylationStableCapacity.CoalescedSecondOrder

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section

/-- A second-order Chebyshev-type sequence with `F₀=1` and `F₁=2t+1`. -/
def coalescedChebF : ℕ → ℝ → ℝ
  | 0, _ => 1
  | 1, t => 2 * t + 1
  | n + 2, t =>
      2 * t * coalescedChebF (n + 1) t - coalescedChebF n t

theorem coalescedN_scaled_of_relations (u t lam : ℝ)
    (htrace : 20 + 16 * u = 2 * t * lam)
    (hdet : 64 * (u - 1) ^ 2 = lam ^ 2)
    (hbase : 28 + 8 * u = lam * (2 * t + 1)) (m : ℕ) :
    (coalescedPair m).1.eval u = lam ^ m * coalescedChebF m t := by
  induction m using Nat.twoStepInduction with
  | zero => simp [coalescedN_eval_zero, coalescedChebF]
  | one =>
      rw [coalescedN_eval_one, hbase]
      simp [coalescedChebF]
  | more m ih0 ih1 =>
      rw [coalescedN_eval_add_two, ih1, ih0, htrace, hdet]
      change 2 * t * lam * (lam ^ (m + 1) * coalescedChebF (m + 1) t) -
        lam ^ 2 * (lam ^ m * coalescedChebF m t) =
        lam ^ (m + 2) *
          (2 * t * coalescedChebF (m + 1) t - coalescedChebF m t)
      rw [pow_add, pow_succ]
      ring

def coalescedLam (u : ℝ) : ℝ := 8 * (1 - u)

def coalescedT (u : ℝ) : ℝ := (5 + 4 * u) / (4 * (1 - u))

/-- Exact conjugacy between the literal coalesced source and the
Chebyshev-type recurrence away from `u=1`. -/
theorem coalescedN_cheb_scale (m : ℕ) (u : ℝ) (hu : u ≠ 1) :
    (coalescedPair m).1.eval u =
      coalescedLam u ^ m * coalescedChebF m (coalescedT u) := by
  have hden : 1 - u ≠ 0 := by
    intro h
    apply hu
    linarith
  have htrace : 20 + 16 * u =
      2 * coalescedT u * coalescedLam u := by
    unfold coalescedT coalescedLam
    field_simp [hden]
    ring
  have hdet : 64 * (u - 1) ^ 2 = coalescedLam u ^ 2 := by
    unfold coalescedLam
    ring
  have hbase : 28 + 8 * u =
      coalescedLam u * (2 * coalescedT u + 1) := by
    unfold coalescedT coalescedLam
    field_simp [hden]
    ring
  exact coalescedN_scaled_of_relations u (coalescedT u)
    (coalescedLam u) htrace hdet hbase m

end
end PhosphorylationStableCapacity
