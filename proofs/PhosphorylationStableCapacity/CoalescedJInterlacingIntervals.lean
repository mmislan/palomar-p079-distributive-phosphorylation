module
public import Mathlib.Analysis.Polynomial.Basic
public import Mathlib.Topology.Algebra.Polynomial
public import proofs.PhosphorylationStableCapacity.CoalescedJRootAlternation

@[expose] public section

namespace PhosphorylationStableCapacity

open Polynomial

noncomputable section

theorem polynomial_zero_between_of_opposite {p : ℝ[X]} {a b : ℝ}
    (hab : a < b) (hopp : p.eval a * p.eval b < 0) :
    ∃ x : ℝ, a < x ∧ x < b ∧ p.eval x = 0 := by
  have hc : Continuous (fun x : ℝ => p.eval x) := by fun_prop
  rcases mul_neg_iff.mp hopp with ⟨ha, hb⟩ | ⟨ha, hb⟩
  · obtain ⟨x, hx, hfx⟩ :=
      (intermediate_value_Ioo' hab.le hc.continuousOn)
        (show (0 : ℝ) ∈ Set.Ioo (p.eval b) (p.eval a) from ⟨hb, ha⟩)
    exact ⟨x, hx.1, hx.2, hfx⟩
  · obtain ⟨x, hx, hfx⟩ :=
      (intermediate_value_Ioo hab.le hc.continuousOn)
        (show (0 : ℝ) ∈ Set.Ioo (p.eval a) (p.eval b) from ⟨ha, hb⟩)
    exact ⟨x, hx.1, hx.2, hfx⟩

theorem coalescedJ_adjacent_opposite (m j : ℕ) (hj : j + 1 < m) :
    (coalescedPair m).2.eval (coalescedRoot m (j + 1)) *
      (coalescedPair m).2.eval (coalescedRoot m j) < 0 := by
  have hjm : j < m := by omega
  have h1 := coalescedJ_at_N_root_alternating m j hjm
  have h2 := coalescedJ_at_N_root_alternating m (j + 1) hj
  have hpow : (-1 : ℝ) ^ ((j + 1) + 1) =
      -((-1 : ℝ) ^ (j + 1)) := by rw [pow_succ]; ring
  rw [hpow] at h2
  by_cases he : Even (j + 1)
  · have hs : (-1 : ℝ) ^ (j + 1) = 1 := Even.neg_one_pow he
    rw [hs] at h1 h2
    have hJ1 : 0 < (coalescedPair m).2.eval (coalescedRoot m j) := by
      simpa using h1
    have hJ2 : (coalescedPair m).2.eval (coalescedRoot m (j + 1)) < 0 := by
      nlinarith [h2]
    exact mul_neg_of_neg_of_pos hJ2 hJ1
  · have ho : Odd (j + 1) := Nat.not_even_iff_odd.mp he
    have hs : (-1 : ℝ) ^ (j + 1) = -1 := Odd.neg_one_pow ho
    rw [hs] at h1 h2
    have hJ1 : (coalescedPair m).2.eval (coalescedRoot m j) < 0 := by
      nlinarith [h1]
    have hJ2 : 0 < (coalescedPair m).2.eval (coalescedRoot m (j + 1)) := by
      nlinarith [h2]
    exact mul_neg_of_pos_of_neg hJ2 hJ1

theorem coalescedJ_zero_between_adjacent (m j : ℕ) (hj : j + 1 < m) :
    ∃ x : ℝ,
      coalescedRoot m (j + 1) < x ∧ x < coalescedRoot m j ∧
        (coalescedPair m).2.eval x = 0 := by
  exact polynomial_zero_between_of_opposite
    (coalescedRoot_strictAnti m j (j + 1) (by omega) hj (by omega))
    (coalescedJ_adjacent_opposite m j hj)

end
end PhosphorylationStableCapacity
