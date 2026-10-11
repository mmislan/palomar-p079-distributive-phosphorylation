module
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Int.Cast.Lemmas
public import Lean.Elab.Tactic.Omega
public import Lean.Elab.Tactic.NormCast

@[expose] public section

namespace PhosphorylationStableCapacity

noncomputable section

/-- Arithmetic core of the stable-state ceiling after a regular
perturbation: stable points have index `+1`, all other regular points
have index at least `-1`, total degree is `+1`, and at most `2n`
regular equilibria exist. The analytic perturbation and degree inputs
are separate proof obligations. -/
theorem stable_index_count_le_of_regular_budget
    {α : Type*} [DecidableEq α]
    (stable other : Finset α) (index : α → ℤ) (n : ℕ)
    (hstable : ∀ x ∈ stable, index x = 1)
    (hother : ∀ x ∈ other, -1 ≤ index x)
    (hdegree : (∑ x ∈ stable, index x) +
      (∑ x ∈ other, index x) = 1)
    (hbudget : stable.card + other.card ≤ 2*n) :
    stable.card ≤ n := by
  have hs : (∑ x ∈ stable, index x) = (stable.card : ℤ) := by
    calc
      (∑ x ∈ stable, index x) = ∑ _x ∈ stable, (1 : ℤ) := by
        apply Finset.sum_congr rfl
        intro x hx
        exact hstable x hx
      _ = (stable.card : ℤ) := by simp
  have ho : -(other.card : ℤ) ≤ ∑ x ∈ other, index x := by
    have hsum : (∑ _x ∈ other, (-1 : ℤ)) ≤
        ∑ x ∈ other, index x := by
      apply Finset.sum_le_sum
      intro x hx
      exact hother x hx
    simpa using hsum
  have hbudget_int : (stable.card : ℤ) + (other.card : ℤ) ≤
      2 * (n : ℤ) := by exact_mod_cast hbudget
  omega

end
end PhosphorylationStableCapacity
