module
public import proofs.PhosphorylationStableCapacity.RationalExpressionIntervals
public import Mathlib.Algebra.BigOperators.Fin

@[expose] public section

namespace PhosphorylationStableCapacity.RationalExpression
open scoped BigOperators

/-- A finite rational linear combination with a structural evaluation proof.
The coefficients may be precontracted before interval evaluation, preserving
the cancellation that would otherwise be lost in interval matrix products. -/
def linearCombination {σ : Type*} : (n : ℕ) →
    (Fin n → ℚ) → (Fin n → RationalExpression σ) → RationalExpression σ
  | 0, _, _ => .const 0
  | n+1, c, e => .add (.mul (.const (c 0)) (e 0))
      (linearCombination n (fun i => c i.succ) (fun i => e i.succ))

theorem eval_linearCombination {σ : Type*} (v : σ → ℝ) (n : ℕ)
    (c : Fin n → ℚ) (e : Fin n → RationalExpression σ) :
    (linearCombination n c e).eval v = ∑ i, (c i : ℝ)*(e i).eval v := by
  induction n with
  | zero => simp [linearCombination, eval]
  | succ n ih =>
    simp only [linearCombination, eval, Fin.sum_univ_succ]
    rw [ih]

end PhosphorylationStableCapacity.RationalExpression
