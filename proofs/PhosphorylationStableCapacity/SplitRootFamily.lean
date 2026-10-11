module
public import proofs.PhosphorylationStableCapacity.CoalescedMoments

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section

open PhosphorylationSharpness Polynomial

/-- An ordered family of roots that all coalesce at `3` when `δ=0`. -/
def splitRoot (δ : ℝ) (j : ℕ) : ℝ := 3 + δ * j

/-- The inherited paired-root recurrence, now with one common splitting
parameter. The pair added at step `m` has root indices `2m+1,2m+2`. -/
def splitPair : ℕ → ℝ → ℝ[X] × ℝ[X]
  | 0, _ => (1, 1)
  | m + 1, δ =>
      let pq := splitPair m δ
      (nextN (splitRoot δ (2*m+1)) (splitRoot δ (2*m+2)) pq.1 pq.2,
       nextJ (splitRoot δ (2*m+1)) (splitRoot δ (2*m+2)) pq.1 pq.2)

/-- At zero splitting the family is exactly the previously certified
coalesced source, not merely another matrix with similar eigenvalues. -/
theorem splitPair_zero_eq_coalesced (m : ℕ) :
    splitPair m 0 = coalescedPair m := by
  induction m with
  | zero => rfl
  | succ m ih =>
      simp [splitPair, coalescedPair, splitRoot, ih]

/-- Every source coefficient remains strictly positive before conversion
for nonnegative splitting parameters. -/
theorem splitPair_dense (m : ℕ) {δ : ℝ} (hδ : 0 ≤ δ) :
    DensePositive (splitPair m δ).1 m ∧
      DensePositive (splitPair m δ).2 m := by
  induction m with
  | zero =>
      exact ⟨by simpa [splitPair] using dense_constant 1 (by norm_num),
        by simpa [splitPair] using dense_constant 1 (by norm_num)⟩
  | succ m ih =>
      have ha : 1 < splitRoot δ (2*m+1) := by
        have hh : 0 ≤ δ * ((2*m+1 : ℕ) : ℝ) :=
          mul_nonneg hδ (Nat.cast_nonneg _)
        dsimp [splitRoot]
        linarith
      have hb : 1 < splitRoot δ (2*m+2) := by
        have hh : 0 ≤ δ * ((2*m+2 : ℕ) : ℝ) :=
          mul_nonneg hδ (Nat.cast_nonneg _)
        dsimp [splitRoot]
        linarith
      exact next_dense ih.1 ih.2 ha hb

/-- Each of the `2m+1` prescribed values is an exact root of the
source's scalar reduction, uniformly in the splitting parameter. -/
theorem splitPair_roots (m j : ℕ) (δ : ℝ) (hj : j ≤ 2*m) :
    (splitRoot δ j - 1) *
        (splitPair m δ).1.eval (ratio (splitRoot δ j)) -
      2 * (splitPair m δ).2.eval (ratio (splitRoot δ j)) = 0 := by
  induction m with
  | zero =>
      have : j = 0 := by omega
      subst j
      norm_num [splitPair, splitRoot]
  | succ m ih =>
      change _ * (nextN _ _ _ _).eval _ -
        2 * (nextJ _ _ _ _).eval _ = 0
      rw [next_identity]
      by_cases h : j ≤ 2*m
      · rw [ih h]
        ring
      · have hcases : j = 2*m+1 ∨ j = 2*m+2 := by omega
        rcases hcases with h | h <;> subst j <;>
          simp only [splitRoot] <;> push_cast <;> ring

/-- Positive splitting makes all prescribed roots distinct, while they
still converge to the same coalesced value as `δ→0`. -/
theorem splitRoot_strictMono {δ : ℝ} (hδ : 0 < δ) :
    StrictMono (splitRoot δ) := by
  intro i j hij
  have hcast : (i : ℝ) < (j : ℝ) := by exact_mod_cast hij
  dsimp [splitRoot]
  simpa [add_comm] using
    (add_lt_add_left (mul_lt_mul_of_pos_left hcast hδ) 3)

end
end PhosphorylationStableCapacity
